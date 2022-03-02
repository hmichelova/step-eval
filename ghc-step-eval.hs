{-# LANGUAGE TemplateHaskell #-}
module Ghc_step_eval where

import Control.Monad
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Data.Maybe ( isNothing )
import Prelude hiding ( map, filter, id, take, const, last )

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

isNone :: EitherNone Exp -> Bool
isNone None = True
isNone _    = False

fromValue :: EitherNone Exp -> Exp
fromValue (Value exp) = exp
fromValue x           = error ("Function `fromValue` is used for: " ++ show x)

step :: Exp -> [Dec] -> EitherNone Exp
step (LitE _) _ = None
step (VarE _) _ = None -- TODO check if it is possible to rewrite
step (ConE _) _ = None
step exp@(AppE exp1 exp2) d = let (hexp : exps) = getSubExp exp1 ++ [exp2] in
  applyExp hexp exps
  where
    getSubExp :: Exp -> [Exp]
    getSubExp (AppE exp1 exp2) = getSubExp exp1 ++ [exp2]
    getSubExp x                = [x] -- TODO check if correct

    applyExp :: Exp -> [Exp] -> EitherNone Exp
    applyExp hexp@(VarE x) exps = let decs = filterByName (getName hexp) False d in
      let exps' = expsToWHNF exps in
        if all isNone exps'
          then processDecs exps decs
          else makeAppE (hexp : replaceAtIndex (length exps' - 1) (last exps') exps)
    applyExp e@(InfixE _ _ _) [] = Exception ("Function application `" ++ show (pprint e) ++ "` has no arguments")
    applyExp ie@(InfixE me1 exp me2) (e : exps) = let enexp' = step exp d in
      case enexp' of
        Exception e -> Exception e
        None -> substituteNothingInInfixE ie e >>= \ie' -> makeAppE (ie' : exps)
        Value exp' -> makeAppE (exp' : makeListArgsInfixE me1 me2 e ++ exps)
      where
        substituteNothingInInfixE :: Exp -> Exp -> EitherNone Exp
        substituteNothingInInfixE ie@(InfixE me1 exp me2) e
          | isNothing me1 = Value $ InfixE (Just e) exp me2
          | isNothing me2 = Value $ InfixE me1 exp (Just e)
          | otherwise     = Exception ("Infix expression `" ++ show (pprint ie) ++ "` have all arguments - application is not allowed")

        makeListArgsInfixE :: Maybe Exp -> Maybe Exp -> Exp -> [Exp]
        makeListArgsInfixE Nothing Nothing e = [e]
        makeListArgsInfixE Nothing (Just e2) e = [e, e2]
        makeListArgsInfixE (Just e1) Nothing e = [e1, e]
        makeListArgsInfixE (Just e1) (Just e2) e = [e1, e2, e]

    applyExp hexp exps = step hexp d >>= \exp1' -> makeAppE (exp1' : exps)

    makeAppE :: [Exp] -> EitherNone Exp
    makeAppE []  = Exception "Something went terribly wrong"
    makeAppE [x] = Value x
    makeAppE (x : y : xs) = makeAppE (AppE x y : xs)

    expsToWHNF :: [Exp] -> [EitherNone Exp]
    expsToWHNF [] = []
    expsToWHNF (x : xs) = let x' = toWHNF x in
      if isNone x'
        then None : expsToWHNF xs
        else [x']

    replaceAtIndex :: Int -> EitherNone Exp -> [Exp] -> [Exp]
    replaceAtIndex i (Value x) xs = take i xs ++ [x] ++ drop (i + 1) xs

step ie@(InfixE me1 exp me2) d = let enexp' = step exp d in
  case enexp' of
    Exception e -> Exception e
    None -> let eie1' = stepMaybe me1 d in
      case eie1' of
        Exception e -> Exception e
        None -> let eie2' = stepMaybe me2 d in
          case eie2' of
            Exception e -> Exception e
            None -> let val = LitE (IntegerL 42) in -- TODO fix with interpreter
                Value $ val
            Value e2' -> Value $ InfixE me1 exp (Just e2')
        Value e1' -> Value $ InfixE (Just e1') exp me2
    Value exp' -> Value $ InfixE me1 exp' me2 -- TODO fix?
  where
    stepMaybe :: Maybe Exp -> [Dec] -> EitherNone Exp
    stepMaybe Nothing _ = None
    stepMaybe (Just e) d = step e d

step (CondE b t f) d = let b' = step b d in
  case b' of
    Exception e -> Exception e
    None -> case b of
      ConE (Name (OccName n) _) -> if n == "True" then Value $ t else Value $ f
      otherwise -> Exception $ "Condition `" ++ pprint b ++ "` can't be evaluate to Bool expression"
    Value v -> Value $ CondE v t f

step exp _ = Exception ("Unsupported format of expression: " ++ pprint exp)


filterByName :: String -> Bool -> [Dec] -> [Dec]
filterByName n sign xs = filter theSameName xs
  where
    theSameName :: Dec -> Bool
    theSameName (SigD (Name (OccName name) _) _) = sign && n == name
    theSameName (FunD (Name (OccName name) _) _) = n == name
    theSameName _                                = False

patMatch :: Pat -> Exp -> EitherNone [(Name, Exp)]
patMatch WildP _ = Value []
patMatch (LitP lp) (LitE le) = if lp == le then Value [] else None
patMatch p@(LitP lp) exp = {-let (e, b) = step exp decs in
  if b
    then patMatch p e
    else -} None -- TODO fix
patMatch (VarP n) exp       = Value [(n, exp)]
patMatch (TupP ps) (TupE es) = if length ps /= length es then None
  else patMatchTup ps es
  where
    patMatchTup :: [Pat] -> [Maybe Exp] -> EitherNone [(Name, Exp)]
    patMatchTup [] [] = Value []
    patMatchTup (p : pats) (Just e : exps) = patMatch p e >>=
      \m1 -> patMatchTup pats exps >>=
      \m2 -> Value (m1 ++ m2)
    patMatchTup (p : pats) (Nothing : exps) = patMatchTup pats exps -- TODO check
    patMatchTup _ _ = Exception "Something went wrong in tuples check"
patMatch (ConP np _ []) (ConE ne) = if np == ne then Value [] else None
patMatch (ConP np _ _) (ConE ne) = undefined -- TODO AppE
patMatch (AsP n p) exp       = patMatch p exp >>=
  \m -> Value ((n, exp) : m) -- TODO check
patMatch (ParensP p) exp     = patMatch p exp
patMatch (ListP ps) (ListE es) = if length ps /= length es then None
  else checkLists ps es
  where
    checkLists :: [Pat] -> [Exp] -> EitherNone [(Name, Exp)]
    checkLists [] [] = Value []
    checkLists (p : pats) (e : exps) = patMatch p e >>=
      \m1 -> checkLists pats exps >>=
      \m2 -> Value (m1 ++ m2)
    checkLists _ _ = Exception "Something went wrong in lists check"
patMatch (InfixP p1 np p2) (InfixE (Just e1) exp (Just e2)) = patMatch p1 e1 >>=
  \m1 -> patMatch (ConP np [] []) exp >>= -- TODO check
  \mp -> patMatch p2 e2 >>=
  \m2 -> Value (m1 ++ mp ++ m2)
patMatch _ _ = None -- TODO

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
    else replaceOrContinue $ patsMatch exps pats
  where
    replaceOrContinue :: EitherNone [(Name, Exp)] -> EitherNone Exp
    replaceOrContinue (Exception e) = Exception e
    replaceOrContinue None = processDecs exps ((FunD n clauses) : decs)
    replaceOrContinue (Value m) = Value (replaceVars e m)

processDecs exps (FunD n (Clause pats (GuardedB gb) _ : clauses) : decs) = undefined -- TODO

patsMatch :: [Exp] -> [Pat] -> EitherNone [(Name, Exp)]
patsMatch (e : exps) (p : pats) = patMatch p e >>=
  \m1 -> patsMatch exps pats >>=
  \m2 -> Value (m1 ++ m2)
patsMatch [] [] = Value []
patsMatch [] p =
  Exception ("Number of arguments (0) and " ++
             "number of paterns (" ++ show (length p) ++ ") are not the same")
patsMatch e p =
  Exception ("Number of arguments (" ++ show (length e) ++ ") and " ++
             "number of paterns (" ++ show (length p) ++ ") are not the same") -- TODO fix etared


toWHNF :: Exp -> EitherNone Exp
toWHNF (CompE stmts) = undefined -- TODO fix
toWHNF (ArithSeqE range) = undefined -- TODO fix
toWHNF (ListE []) = Value (ConE '[])
toWHNF (ListE (x : xs)) = Value (InfixE (Just x) (ConE '(:)) (Just (ListE xs)))
toWHNF exp = None

myTry :: Q Exp -> Q [Dec] -> IO ()
myTry qexp qdec = do
  e <- runQ qexp
  d <- runQ qdec
  nextStep (Value e) d
  where
    niceOutputPrint :: EitherNone Exp -> IO ()
    niceOutputPrint (Exception e) = fail e
    niceOutputPrint None = putStrLn "Return value is none"
    niceOutputPrint (Value e) = putStrLn $ pprint e

    nextStep :: EitherNone Exp -> [Dec] -> IO ()
    nextStep ene@(Value e) d = do
        niceOutputPrint ene
        let ene1 = step e d
        nextStep ene1 d
    nextStep None _ = putStrLn "No next steps"
    nextStep (Exception e) _ = fail e

