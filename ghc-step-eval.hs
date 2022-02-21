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
    then let decs = filterByName (getName hexp) False d in
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
step (InfixE mexpr1 expr mexpr2) _ = undefined

step exp _ = error ("Unsupported format of expression: " ++ pprint exp)


filterByName :: String -> Bool -> [Dec] -> [Dec]
filterByName n sign xs = filter theSameName xs
  where
    theSameName :: Dec -> Bool
    theSameName (SigD (Name (OccName name) _) _) = sign && n == name
    theSameName (FunD (Name (OccName name) _) _) = n == name
    theSameName _                                = False

checkPat :: Pat -> Exp -> ([(Name, Exp)], Bool)
checkPat WildP _ = ([], True)
checkPat (LitP lp) (LitE le) = ([], lp == le)
checkPat p@(LitP lp) exp = {-let (e, b) = step exp decs in
  if b
    then checkPat p e
    else -} ([], False) -- TODO fix
checkPat (VarP n) exp       = ([(n, exp)], True)
checkPat (TupP ps) (TupE es) = if length ps /= length es then ([], False)
  else checkTups ps es
  where
    checkTups :: [Pat] -> [Maybe Exp] -> ([(Name, Exp)], Bool)
    checkTups [] [] = ([], True)
    checkTups (p : pats) (Just e : exps) = let (m, b) = checkPat p e in
      if b 
        then let (m2, b2) = checkTups pats exps in
          if b2
            then (m ++ m2, True)
            else ([], False)
        else ([], False)
    checkTups (p : pats) (Nothing : exps) = checkTups pats exps -- TODO check
    checkTups _ _ = error "Something went wrong in tuples check"
checkPat (ConP np _ _) (ConE ne) = ([], np == ne) -- TODO add AppE
checkPat (AsP n p) exp       = undefined -- TODO recursion
checkPat (ParensP p) exp     = checkPat p exp
checkPat (ListP ps) (ListE es) = if length ps /= length es then ([], False)
  else checkLists ps es
  where
    checkLists :: [Pat] -> [Exp] -> ([(Name, Exp)], Bool)
    checkLists [] [] = ([], True)
    checkLists (p : pats) (e : exps) = let (m, b) = checkPat p e in
      if b 
        then let (m2, b2) = checkLists pats exps in
          if b2
            then (m ++ m2, True)
            else ([], False)
        else ([], False)
    checkLists _ _ = error "Something went wrong in lists check"
checkPat (ListP ps) (CompE stmts) = undefined -- TODO
checkPat (ListP ps) (ArithSeqE range) = undefined -- TODO
checkPat (InfixP p1 np p2) (InfixE m1 exp m2) = undefined -- TODO
checkPat (InfixP p1 (Name (OccName ":") _) p2) (ListE (x : xs)) = 
  let (x1, b1) = checkPat p1 x in
    if not b1 then ([], False)
    else let (x2, b2) = checkPat p2 (ListE xs) in
      if not b2 then ([], False)
      else (x1 ++ x2, True)
checkPat _ _ = ([], False) -- TODO

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

isVar :: Exp -> Bool
isVar (VarE _) = True
isVar _        = False

getName :: Exp -> String
getName (VarE (Name (OccName n) _)) = n
getName _ = error "Given expression is not variable expression"

processDecs :: Exp -> [Exp] -> [Dec] -> (Exp, Bool)
processDecs origExp _    [] = (origExp, False)
processDecs origExp exps (FunD n [] : decs) = processDecs origExp exps decs
processDecs origExp exps (FunD n (Clause pats (NormalB e) _ : clauses) : decs) = -- TODO fix where
  if length exps /= length pats
    then error "Wrong number of argumetns in function ..."
    else let (m, b) = processPats exps pats in
      if b
        then (replaceVars e m, True)
        else processDecs origExp exps ((FunD n clauses) : decs)

processDecs origExp exps (FunD n (Clause pats (GuardedB gb) _ : clauses) : decs) = undefined -- TODO

processPats :: [Exp] -> [Pat] -> ([(Name, Exp)], Bool)
processPats (e : exps) (p : pats) =
  let (m1, b1) = checkPat p e in
    if not b1 then ([], False)
    else let (m2, b2) = processPats exps pats in
      ((if b2 then m1 else []) ++ m2, b2)
processPats [] [] = ([], True)
processPats [] p = 
  error ("Number of arguments (0) and " ++
         "number of paterns (" ++ show (length p) ++ ") are not the same")
processPats e p =
  error ("Number of arguments (" ++ show (length e) ++ ") and " ++
         "number of paterns (" ++ show (length p) ++ ") are not the same") -- TODO fix etared

myTry = do
  e <- runQ myExprMap
  d <- runQ funcs
  putStrLn $ pprint e
  let (e1, b) = step e d
  putStrLn $ show b
  putStrLn $ pprint e1
  let (e2, b2) = step e1 d
  putStrLn $ show b2
  putStrLn $ pprint e2


