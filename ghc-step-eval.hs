{-# LANGUAGE TemplateHaskell #-}
module Ghc_step_eval where

import Control.Monad
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Prelude hiding ( map, filter, id, take, const )

import FunDefs

$funcs

data BinTree a = Empty
               | Node a (BinTree a) (BinTree a)
                 deriving (Show)

instance Eq a => Eq (BinTree a) where
  Empty           == Empty           = True
  (Node v1 l1 r1) == (Node v2 l2 r2) = v1 == v2 && l1 == l2 && r1 == r2
  _               == _               = False

emptyTree :: BinTree Int
emptyTree = Empty

tree42 :: BinTree Int
tree42 = Node 42 Empty Empty

myExprTree :: Q Exp
myExprTree = [| emptyTree |]

myExprTreeEq :: Q Exp
myExprTreeEq = [| emptyTree == tree42 |]

myExprMap :: Q Exp
myExprMap = [| map (+ 2) [1, 2] |]

myExprId :: Q Exp
myExprId = [| id 5 |]

myExprLambda :: Q Exp
myExprLambda = [| \x y ->  y : x |]

myExpr :: Q Exp
myExpr = [| (1 + 2) == (5 * 3) && (7 - 8) < 42 |]

step :: Exp -> [Dec] -> (Exp, Bool)
step x@(LitE _) _ = (x, False)
step x@(VarE _) _ = (x, False)
step exp@(AppE exp1 exp2) d = 
  let (hexp : exps) = getSubExp exp1 ++ [exp2] in
  if isVar hexp
    then let decs = filterByName (name hexp) False d in
      processDecs exp exps decs
    else let (exp1', b) = step hexp d in
      (makeAppE (exp1' : exps), True)

  where
    getSubExp :: Exp -> [Exp]
    getSubExp (AppE exp1 exp2) = getSubExp exp1 ++ [exp2]
    getSubExp x                = [x] -- TODO check if correct

    makeAppE :: [Exp] -> Exp
    makeAppE []  = error "Something went terribly wrong"
    makeAppE [x] = x
    makeAppE (x : y : xs) = makeAppE (AppE x y : xs)

    isVar :: Exp -> Bool
    isVar (VarE _) = True
    isVar _        = False

    name :: Exp -> String
    name (VarE (Name (OccName name) _)) = name

    processDecs :: Exp -> [Exp] -> [Dec] -> (Exp, Bool)
    processDecs origExp _    [] = (origExp, False)
    processDecs origExp exps (FunD n (Clause pats (NormalB e) _ : clauses) : decs) = -- TODO fix where and body and clauses?
      if length exps /= length pats then error "Wrong number of argumetns in function ..."
      else let (b, m) = processPats exps pats in
        if b
          then (replaceVars e m, True)
          else if null clauses
            then processDecs origExp exps decs
            else processDecs origExp exps ((FunD n clauses) : decs)

    processDecs origExp exps decs = error ("Number: " ++ show (length decs))

    processPats :: [Exp] -> [Pat] -> (Bool, [(Name, Exp)])
    processPats (e : exps) (p : pats) =
      let (b1, m1) = checkPat p e in
        if not b1 then (False, [])
        else let (b2, m2) = processPats exps pats in
          (b2, (if b2 then m1 else []) ++ m2)
    processPats [] [] = (True, [])

    processPats e p = error ("Number of arguments (" ++ show (length e) ++ ") and number of paterns (" ++ show (length p) ++ ") are not the same") -- TODO fix etareduction
          

step (InfixE mexpr1 expr mexpr2) _ = undefined

step exp _ = error ("Unsupported format of expression: " ++ pprint exp)


filterByName :: String -> Bool -> [Dec] -> [Dec]
filterByName n sign xs = filter theSameName xs
  where
    theSameName :: Dec -> Bool
    theSameName (SigD (Name (OccName name) _) _) = sign && n == name
    theSameName (FunD (Name (OccName name) _) _) = n == name
    theSameName _                                = False

checkPat :: Pat -> Exp -> (Bool, [(Name, Exp)])
checkPat WildP _ = (True, [])
checkPat (LitP lp) (LitE le) = (lp == le, [])
checkPat (LitP lp) _         = (False, []) -- TODO fix to eval exp
checkPat (VarP n)  exp       = (True, [(n, exp)])
checkPat (TupP ps) (TupE es) = undefined -- TODO make recursion
checkPat (ConP np _ _) (ConE ne) = (np == ne, []) -- TODO add AppE
checkPat (AsP n p) exp       = undefined -- TODO recursion
checkPat (ParensP p) exp     = checkPat p exp
checkPat (ListP ps) (ListE es) = undefined -- TODO
checkPat (InfixP p1 np p2) (InfixE m1 exp m2) = undefined -- TODO
checkPat (InfixP p1 (Name (OccName ":") _) p2) (ListE (x : xs)) = 
  let (b1, x1) = checkPat p1 x in
    if not b1 then (False, [])
    else let (b2, x2) = checkPat p2 (ListE xs) in
      if not b2 then (False, [])
      else (True, x1 ++ x2)
checkPat _ _ = (False, []) -- TODO

replaceVars :: Exp -> [(Name, Exp)] -> Exp
replaceVars = foldl (\exp (Name (OccName s) _, e) -> replaceVar exp s e)

replaceVar :: Exp -> String -> Exp -> Exp
replaceVar exp@(VarE (Name (OccName n) _)) s e = if n == s then e else exp
replaceVar (AppE e1 e2) s e = AppE (replaceVar e1 s e) (replaceVar e2 s e)
replaceVar (InfixE me1 exp me2) s e =
  InfixE (maybe Nothing (\e1 -> Just (replaceVar e1 s e)) me1)
         (replaceVar exp s e)
         (maybe Nothing (\e2 -> Just (replaceVar e2 s e)) me2)
replaceVar (ParensE exp) s e = ParensE (replaceVar exp s e)
replaceVar (LamE pats exp) s e = undefined -- TODO
replaceVar exp _ _ = exp -- TODO


myTry = do
  e <- runQ myExprMap
  d <- runQ funcs
  putStrLn $ pprint e
  let (e1, b) = step e d
  putStrLn $ show b
  putStrLn $ pprint e1


