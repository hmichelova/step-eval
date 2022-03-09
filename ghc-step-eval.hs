{-# LANGUAGE TemplateHaskell, OverloadedStrings #-}
module Ghc_step_eval where

import Control.Monad
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Data.Maybe ( isNothing )
import Prelude hiding ( map, filter, id, take, const, last )
import Data.Text (pack, unpack, replace)
import Language.Haskell.Interpreter
import qualified Data.Map as M
import qualified Control.Monad.Trans.State.Lazy as S

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

myEmpty :: Q Exp
myEmpty = [| Empty |]

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

type IOEitherNone a = IO (EitherNone a)

type Env a = M.Map Name a

evalInterpreter :: Exp -> IOEitherNone Exp
evalInterpreter e = do
  r <- runInterpreter $ doInterpret $ replaces $ pprint e
  case r of
    Left err -> pure $ Exception $ show err
    Right qe -> do
      e' <- runQ qe
      pure $ Value e'
  where
    doInterpret s = do
      setImports moduleList
      r <- interpret s (as :: Integer) -- TODO
      pure $ [| r |]

    moduleList :: [ModuleName]
    moduleList = ["Prelude", "GHC.Num", "GHC.Base", "GHC.Types"]

    replaces :: String -> String
    replaces = unpack . replace "GHC.Types." "" . pack

isNone :: EitherNone Exp -> Bool
isNone None = True
isNone _    = False

fromValue :: EitherNone Exp -> Exp
fromValue (Value exp) = exp
fromValue x           = error ("Function `fromValue` is used for: " ++ show x)

step :: Exp -> [Dec] -> S.StateT (Env Exp) IO (EitherNone Exp)
step (LitE _) _ = pure None
step (VarE x) d = do
  env <- S.get
  case M.lookup x env of
    Just exp -> do
      exp' <- step exp d
      case exp' of
        Exception e -> pure $ Exception e
        None -> pure None
        Value v -> do
          S.put $ M.adjust (\_ -> v) x env
          pure $ Value $ (VarE x)
    Nothing -> pure None -- TODO no value is ok?
step (ConE _) _ = pure None
step exp@(AppE exp1 exp2) d = let (hexp : exps) = getSubExp exp1 ++ [exp2] in
  applyExp hexp exps
  where
    getSubExp :: Exp -> [Exp]
    getSubExp (AppE exp1 exp2) = getSubExp exp1 ++ [exp2]
    getSubExp x                = [x] -- TODO check if correct

    applyExp :: Exp -> [Exp] -> S.StateT (Env Exp) IO (EitherNone Exp)
    applyExp hexp@(VarE x) exps = let decs = filterByName (getName hexp) False d in
      let exps' = expsToWHNF exps in
        if all isNone exps'
          then pure $ processDecs exps decs
          else pure $ makeAppE (hexp : replaceAtIndex (length exps' - 1) (last exps') exps)
    applyExp e@(InfixE _ _ _) [] = pure $ Exception $ "Function application `" ++ show (pprint e) ++ "` has no arguments"
    applyExp ie@(InfixE me1 exp me2) (e : exps) = do
      enexp' <- step exp d
      case enexp' of
        Exception e -> pure $ Exception e
        None -> pure $ substituteNothingInInfixE ie e >>= \ie' -> makeAppE (ie' : exps)
        Value exp' -> pure $ makeAppE (exp' : makeListArgsInfixE me1 me2 e ++ exps)
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

    applyExp hexp exps = do
      nexp1' <- step hexp d
      case nexp1' of
        Value exp1' -> pure $ makeAppE (exp1' : exps)
        x           -> pure x

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

step ie@(InfixE me1 exp me2) d = do
  enexp' <- step exp d
  case enexp' of
    Exception e -> pure $ Exception e
    None -> do
      eie1' <- stepMaybe me1 d
      case eie1' of
        Exception e -> pure $ Exception e
        None -> do
          eie2' <- stepMaybe me2 d
          case eie2' of
            Exception e -> pure $ Exception e
            None -> liftIO $ evalInterpreter ie
            Value e2' -> pure $ Value $ InfixE me1 exp (Just e2')
        Value e1' -> pure $ Value $ InfixE (Just e1') exp me2
    Value exp' -> pure $ Value $ InfixE me1 exp' me2 -- TODO fix?
  where
    stepMaybe :: Maybe Exp -> [Dec] -> S.StateT (Env Exp) IO (EitherNone Exp)
    stepMaybe Nothing _ = pure $ None
    stepMaybe (Just e) d = step e d

step (CondE b t f) d = do
  b' <- step b d
  case b' of
    Exception e -> pure $ Exception e
    None -> case b of
      ConE (Name (OccName n) _) -> pure $ if n == "True" then Value $ t else Value $ f
      otherwise -> pure $ Exception $ "Condition `" ++ pprint b ++ "` can't be evaluate to Bool expression"
    Value v -> pure $ Value $ CondE v t f

step exp _ = pure $ Exception $ "Unsupported format of expression: " ++ pprint exp

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
  process e d
  --nextStep (Value e) d
  where
    process :: Exp -> [Dec] -> IO ()
    process e d = do
      S.runStateT (nextStep (Value e) d) M.empty
      return ()

    niceOutputPrint :: EitherNone Exp -> S.StateT (Env Exp) IO ()
    niceOutputPrint (Exception e) = fail e
    niceOutputPrint None = liftIO $ putStrLn "Return value is none"
    niceOutputPrint (Value e) = liftIO $ putStrLn $ pprint e

    nextStep :: EitherNone Exp -> [Dec] -> S.StateT (Env Exp) IO (EitherNone Exp)
    nextStep ene@(Value e) d = do
      x <- niceOutputPrint ene
      ene1 <- step e d
      nextStep ene1 d
    nextStep None _ = do
      liftIO $ putStrLn "No next steps"
      pure None
    nextStep (Exception e) _ = fail e

