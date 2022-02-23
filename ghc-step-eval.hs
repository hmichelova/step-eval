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

data EitherNone a = Exception String
                  | None
                  | Value a
                    deriving (Eq, Show)

instance Functor EitherNone where
  fmap _ (Exception e) = Exception e
  fmap _ None          = None
  fmap f (Value a)     = Value $ f a

instance Applicative EitherNone where
  pure = Value
  Exception e <*> _ = Exception e
  None        <*> _ = None
  Value f     <*> r = fmap f r

instance Monad EitherNone where
  Exception e >>= _ = Exception e
  None        >>= _ = None
  Value v     >>= f = f v

step :: Exp -> [Dec] -> EitherNone Exp
step x@(LitE _) _ = None
step x@(VarE _) _ = None
step exp@(AppE exp1 exp2) d = 
  let (hexp : exps) = getSubExp exp1 ++ [exp2] in
  if isVar hexp
    then let decs = filterByName (getName hexp) False d in
      processDecs exps decs
    else step hexp d >>= \exp1' -> makeAppE (exp1' : exps)

  where
    getSubExp :: Exp -> [Exp]
    getSubExp (AppE exp1 exp2) = getSubExp exp1 ++ [exp2]
    getSubExp x                = [x] -- TODO check if correct

    makeAppE :: [Exp] -> EitherNone Exp
    makeAppE []  = Exception "Something went terribly wrong"
    makeAppE [x] = Value x
    makeAppE (x : y : xs) = makeAppE (AppE x y : xs)
step (InfixE mexpr1 expr mexpr2) _ = undefined -- TODO

step exp _ = Exception ("Unsupported format of expression: " ++ pprint exp)


filterByName :: String -> Bool -> [Dec] -> [Dec]
filterByName n sign xs = filter theSameName xs
  where
    theSameName :: Dec -> Bool
    theSameName (SigD (Name (OccName name) _) _) = sign && n == name
    theSameName (FunD (Name (OccName name) _) _) = n == name
    theSameName _                                = False

checkPat :: Pat -> Exp -> EitherNone [(Name, Exp)]
checkPat WildP _ = Value []
checkPat (LitP lp) (LitE le) = if lp == le then Value [] else None
checkPat p@(LitP lp) exp = {-let (e, b) = step exp decs in
  if b
    then checkPat p e
    else -} None -- TODO fix
checkPat (VarP n) exp       = Value [(n, exp)]
checkPat (TupP ps) (TupE es) = if length ps /= length es then None
  else checkTups ps es
  where
    checkTups :: [Pat] -> [Maybe Exp] -> EitherNone [(Name, Exp)]
    checkTups [] [] = Value []
    checkTups (p : pats) (Just e : exps) = checkPat p e >>=
      \m1 -> checkTups pats exps >>=
      \m2 -> Value (m1 ++ m2)
    checkTups (p : pats) (Nothing : exps) = checkTups pats exps -- TODO check
    checkTups _ _ = Exception "Something went wrong in tuples check"
checkPat (ConP np _ _) (ConE ne) = if np == ne then Value [] else None -- TODO add AppE
checkPat (AsP n p) exp       = undefined -- TODO recursion
checkPat (ParensP p) exp     = checkPat p exp
checkPat (ListP ps) (ListE es) = if length ps /= length es then None
  else checkLists ps es
  where
    checkLists :: [Pat] -> [Exp] -> EitherNone [(Name, Exp)]
    checkLists [] [] = Value []
    checkLists (p : pats) (e : exps) = checkPat p e >>=
      \m1 -> checkLists pats exps >>=
      \m2 -> Value (m1 ++ m2)
    checkLists _ _ = Exception "Something went wrong in lists check"
checkPat (ListP ps) (CompE stmts) = undefined -- TODO
checkPat (ListP ps) (ArithSeqE range) = undefined -- TODO
checkPat (InfixP p1 np p2) (InfixE m1 exp m2) = undefined -- TODO
checkPat (InfixP p1 (Name (OccName ":") _) p2) (ListE (x : xs)) = checkPat p1 x >>= -- TODO rewrite - skip step
  \x1 -> checkPat p2 (ListE xs) >>=
  \x2 -> Value (x1 ++ x2)
checkPat _ _ = None -- TODO

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

processDecs :: [Exp] -> [Dec] -> EitherNone Exp
processDecs _    [] = None
processDecs exps (FunD n [] : decs) = processDecs exps decs
processDecs exps (FunD n (Clause pats (NormalB e) _ : clauses) : decs) = -- TODO fix where
  if length exps /= length pats
    then Exception "Wrong number of argumetns in function ..."
    else replaceOrContinue $ processPats exps pats
  where
    replaceOrContinue :: EitherNone [(Name, Exp)] -> EitherNone Exp
    replaceOrContinue (Exception e) = Exception e
    replaceOrContinue None = processDecs exps ((FunD n clauses) : decs)
    replaceOrContinue (Value m) = Value (replaceVars e m)

processDecs exps (FunD n (Clause pats (GuardedB gb) _ : clauses) : decs) = undefined -- TODO

processPats :: [Exp] -> [Pat] -> EitherNone [(Name, Exp)]
processPats (e : exps) (p : pats) = checkPat p e >>=
  \m1 -> processPats exps pats >>=
  \m2 -> Value (m1 ++ m2)
processPats [] [] = Value []
processPats [] p = 
  Exception ("Number of arguments (0) and " ++
             "number of paterns (" ++ show (length p) ++ ") are not the same")
processPats e p =
  Exception ("Number of arguments (" ++ show (length e) ++ ") and " ++
             "number of paterns (" ++ show (length p) ++ ") are not the same") -- TODO fix etared

myTry :: IO ()
myTry = do
  e <- runQ myExprMap
  d <- runQ funcs
  putStrLn $ pprint e
  let mee1 = step e d
  niceOutputPrint mee1
  {-mee1 >>= \e1 ->
    let mee2 = step e1 d in niceOutputPrint mee2-}

  where
    niceOutputPrint :: EitherNone Exp -> IO ()
    niceOutputPrint (Exception e) = fail e
    niceOutputPrint None = putStrLn "Return value is none"
    niceOutputPrint (Value e) = putStrLn $ pprint e


