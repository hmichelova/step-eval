{-# LANGUAGE TemplateHaskell, OverloadedStrings #-}
module Ghc_step_eval where

import Control.Monad
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Data.Maybe ( isNothing, fromJust )
import Prelude hiding ( id, const, take, map, filter, last, length, fst, snd, zip, zipWith )
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
    moduleList = ["Prelude", "GHC.Num", "GHC.Base", "GHC.Types", "GHC.Classes", "GHC.List"]

    replaces :: String -> String
    replaces = unpack . replace "GHC.Types." "" . pack

isNone :: EitherNone Exp -> Bool
isNone None = True
isNone _    = False

fromValue :: EitherNone Exp -> Exp
fromValue (Value exp) = exp
fromValue x           = error ("Function `fromValue` is used for: " ++ show x)

step :: Exp -> [Dec] -> S.StateT (Env Exp) IO (EitherNone Exp)
step (VarE x) d = do
  env <- S.get
  case M.lookup x env of
    Just exp -> do
      exp' <- step exp d
      case exp' of
        Exception e -> pure $ Exception e
        None -> pure None
        Value v -> do
          S.put $ M.insert x v env
          pure $ Value $ (VarE x)
    Nothing -> pure None -- TODO no value is ok?

step (ConE _) _ = pure None

step (LitE _) _ = pure None

step exp@(AppE exp1 exp2) d = let (hexp : exps) = getSubExp exp1 ++ [exp2] in
  appExp hexp exps
  where
    getSubExp :: Exp -> [Exp]
    getSubExp (AppE exp1 exp2) = getSubExp exp1 ++ [exp2]
    getSubExp x                = [x] -- TODO check if correct

    appExp :: Exp -> [Exp] -> S.StateT (Env Exp) IO (EitherNone Exp)
    appExp hexp exps = do
      hexp' <- step hexp d
      case hexp' of
        Exception e -> pure $ Exception e
        None -> applyExp hexp exps
        Value v -> pure $ makeAppE (v : exps)

    applyExp :: Exp -> [Exp] -> S.StateT (Env Exp) IO (EitherNone Exp)
    applyExp hexp@(VarE x) exps = do
      let decs = filterByName (getName hexp) False d
      exps' <- expsToWHNF exps 0
      case snd exps' of
        None -> do
          env <- S.get
          if M.member x env
            then applyExp (M.findWithDefault hexp x env) exps
            else processDecs hexp exps decs d
        Value v -> pure $ makeAppE (hexp : replaceAtIndex (fst exps') (Value v) exps)
        x -> pure x
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

    applyExp (UnboundVarE _) _ = undefined

    applyExp hexp exps = do
      nexp1' <- step hexp d
      case nexp1' of
        Value exp1' -> pure $ makeAppE (exp1' : exps)
        x           -> pure x

    expsToWHNF :: [Exp] -> Int -> S.StateT (Env Exp) IO (Int, EitherNone Exp)
    expsToWHNF [] _ = pure (0, None)
    expsToWHNF (x : xs) i = do
      x' <- toWHNF x
      case x' of
        None -> expsToWHNF xs (i + 1)
        _ -> pure (i, x')

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
            None -> do
              env <- S.get
              if isNothing me1 || isNothing me2
                then pure None
                else liftIO $ evalInterpreter $ replaceVars ie $ M.toList env
            Value e2' -> pure $ Value $ InfixE me1 exp (Just e2')
        Value e1' -> pure $ Value $ InfixE (Just e1') exp me2
    Value exp' -> pure $ Value $ InfixE me1 exp' me2 -- TODO fix?

step (ParensE e) d = do
  e' <- step e d
  case e' of
    Value v -> pure $ Value $ ParensE v
    x -> pure x

step (LamE pats exp) d = pure $ Exception "Lambda expressions are not supported yet"

step (TupE []) d = pure None
step exp@(TupE (me : exps)) d = do
  e' <- stepMaybe me d
  case e' of
    None -> do
      exps' <- step (TupE exps) d
      case exps' of
        Value (TupE xs) -> pure $ Value $ TupE $ me : xs
        Value _ -> pure $ Exception $ "Unsupported change of structure in tupple expression " ++ pprint exp
        x -> pure x
    Value v -> pure $ Value $ TupE $ (Just v) : exps
    x -> pure x

step (CondE b t f) d = do
  b' <- step b d
  case b' of
    Exception e -> pure $ Exception e
    None -> case b of
      ConE (Name (OccName n) _) -> pure $ if n == "True" then Value $ t else Value $ f
      otherwise -> pure $ Exception $ "Condition `" ++ pprint b ++ "` can't be evaluate to Bool expression"
    Value v -> pure $ Value $ CondE v t f

step (LetE decs exp) d = pure $ Exception "Let expressions are not supported yet"

step (ListE []) d = pure None
step exp@(ListE (e : exps)) d = do
  e' <- step e d
  case e' of
    None -> do
      exps' <- step (ListE exps) d
      case exps' of
        Value (ListE xs) -> pure $ Value $ ListE $ e : xs
        Value _ -> pure $ Exception $ "Unsupported change of structure in list expression " ++ pprint exp
        x -> pure x
    Value v -> pure $ Value $ ListE $ v : exps
    x -> pure x
  

step exp _ = pure $ Exception $ "Unsupported format of expression: " ++ pprint exp

stepMaybe :: Maybe Exp -> [Dec] -> S.StateT (Env Exp) IO (EitherNone Exp)
stepMaybe Nothing _ = pure $ None
stepMaybe (Just e) d = step e d

makeAppE :: [Exp] -> EitherNone Exp
makeAppE []  = Exception "Something went terribly wrong"
makeAppE [x] = Value x
makeAppE (x : y : xs) = makeAppE (AppE x y : xs)

filterByName :: String -> Bool -> [Dec] -> [Dec]
filterByName n sign xs = filter theSameName xs
  where
    theSameName :: Dec -> Bool
    theSameName (SigD (Name (OccName name) _) _) = sign && n == name
    theSameName (FunD (Name (OccName name) _) _) = n == name
    theSameName _                                = False

-- Note: use only with var replaces Exp
patMatch :: Pat -> Exp -> [Dec] -> S.StateT (Env Exp) IO (Bool, EitherNone Exp)
patMatch WildP _ _ = pure (True, None)
patMatch (LitP lp) (LitE le) _ = pure (lp == le, None)
patMatch p@(LitP lp) exp d = do
  exp' <- step exp d
  pure (False, exp')
patMatch (VarP n) exp _ = do
  env <- S.get
  S.put $ M.insert n exp env
  pure (True, None)
patMatch (TupP ps) (TupE es) d = if length ps /= length es
  then pure (False, None)
  else patMatchTup ps es d
  where
    patMatchTup :: [Pat] -> [Maybe Exp] -> [Dec] -> S.StateT (Env Exp) IO (Bool, EitherNone Exp)
    patMatchTup [] [] _ = pure (True, None)
    patMatchTup (p : pats) (Just e : exps) d = do
      rv <- patMatch p e d
      case rv of
        (True, None) -> do
          rv1 <- patMatchTup pats exps d
          case rv1 of
            (_, Value (TupE exps')) -> pure (False, Value (TupE (Just e : exps')))
            x -> pure x
        (_, Value v) -> pure (False, Value (TupE (Just v : exps)))
        x -> pure x
    patMatchTup (p : pats) (Nothing : exps) d = pure (False, Exception "Missing argument in tuple")
    patMatchTup _ _ _ = pure (False, Exception "Something went wrong in tuples check")
patMatch (ConP np _ []) (ConE ne) _ = pure (np == ne, None)
patMatch (ConP np _ []) (ListE []) _ = pure (np == '[], None)
patMatch (ConP np _ _) (ConE ne) _ = undefined -- TODO AppE
patMatch (AsP n p) exp d = do
  rv <- patMatch p exp d
  case rv of
    (True, None) -> do
      env <- S.get
      S.put $ M.insert n exp env
      pure (True, None)
    x -> pure x
patMatch (ParensP p) exp d = patMatch p exp d
patMatch (ListP ps) (ListE es) d = if length ps /= length es
  then pure (False, None)
  else checkLists ps es d
  where
    checkLists :: [Pat] -> [Exp] -> [Dec] -> S.StateT (Env Exp) IO (Bool, EitherNone Exp)
    checkLists [] [] _ = pure (True, None)
    checkLists (p : pats) (e : exps) d = do
      rv <- patMatch p e d
      case rv of
        (True, None) -> do
          rv1 <- checkLists pats exps d
          case rv1 of
            (_, Value (ListE exps')) -> pure (False, Value (ListE (e : exps')))
            x -> pure x
        (_, Value v) -> pure (False, Value (ListE (v : exps)))
        x -> pure x
    checkLists _ _ _ = pure (False, Exception "Something went wrong in lists check")
patMatch (InfixP p1 np p2) (InfixE (Just e1) exp (Just e2)) d = do
  rv <- patMatch (ConP np [] []) exp d -- TODO check
  case rv of
    (True, None) -> do
      rv1 <- patMatch p1 e1 d
      case rv1 of
        (True, None) -> do
          rv2 <- patMatch p2 e2 d
          case rv2 of
            (_, Value v) -> pure (False, Value (InfixE (Just e1) exp (Just v)))
            x -> pure x
        (_, Value v) -> pure (False, Value (InfixE (Just v) exp (Just e2)))
        x -> pure x
    (_, Value v) -> pure (False, Value (InfixE (Just e1) v (Just e2)))
    x -> pure x
patMatch _ _ _ = pure (False, None) -- TODO

replaceVars :: Exp -> [(Name, Exp)] -> Exp
replaceVars = foldl (\exp (Name (OccName s) _, e) -> replaceVar exp s e)

replaceVar :: Exp -> String -> Exp -> Exp
replaceVar exp@(VarE (Name (OccName n) _)) s e = if n == s then e else exp
replaceVar exp@(ConE _) _ _ = exp
replaceVar exp@(LitE _) _ _ = exp
replaceVar (AppE e1 e2) s e = AppE (replaceVar e1 s e) (replaceVar e2 s e)
replaceVar (InfixE me1 exp me2) s e =
  InfixE (maybe Nothing (\e1 -> Just (replaceVar e1 s e)) me1)
         (replaceVar exp s e)
         (maybe Nothing (\e2 -> Just (replaceVar e2 s e)) me2)
replaceVar (ParensE exp) s e = ParensE (replaceVar exp s e)
replaceVar (LamE pats exp) s e = undefined -- TODO
replaceVar (TupE mexps) s e = TupE $ map (maybe Nothing (\e' -> Just (replaceVar e' s e))) mexps
replaceVar (CondE b t f) s e = CondE (replaceVar b s e) (replaceVar t s e) (replaceVar f s e)
replaceVar (ListE xs) s e = ListE $ map (\exp -> replaceVar exp s e) xs
replaceVar exp _ _ = exp -- TODO

isVar :: Exp -> Bool
isVar (VarE _) = True
isVar _        = False

getName :: Exp -> String
getName (VarE (Name (OccName n) _)) = n
getName _ = error "Given expression is not variable expression"

processDecs :: Exp -> [Exp] -> [Dec] -> [Dec] -> S.StateT (Env Exp) IO (EitherNone Exp)
processDecs hexp [exp1, exp2] [] _ = pure $ Value $ AppE (InfixE (Just exp1) hexp Nothing) exp2
processDecs hexp exps [] _ = let appE = makeAppE (hexp : exps) in
  case appE of
    Value v -> liftIO $ evalInterpreter v
    x -> pure x
processDecs hexp exps (FunD n [] : decs) d = processDecs hexp exps decs d
processDecs hexp exps (FunD n (Clause pats (NormalB e) _ : clauses) : decs) d = do-- TODO fix where
  if length exps /= length pats
    then pure $ Exception "Wrong number of arguments in function ..."
    else do
      exp' <- patsMatch hexp exps pats d
      changeOrContinue exp'
  where
    changeOrContinue :: (Bool, EitherNone Exp) -> S.StateT (Env Exp) IO (EitherNone Exp)
    changeOrContinue (_, (Exception e)) = pure $ Exception e
    changeOrContinue (False, None) = processDecs hexp exps ((FunD n clauses) : decs) d
    changeOrContinue (True, None) = pure $ Value e
    changeOrContinue (_, changedValue) = pure changedValue

processDecs hexp exps (FunD n (Clause pats (GuardedB gb) _ : clauses) : decs) d = pure $ Exception "Guards are not supported"

patsMatch :: Exp -> [Exp] -> [Pat] -> [Dec] -> S.StateT (Env Exp) IO (Bool, EitherNone Exp)
patsMatch hexp (e : exps) (p : pats) d = do
  originEnv <- S.get
  rv <- patMatch p (replaceVars e (M.toList originEnv)) d
  case rv of
    (True, None) -> patsMatch (AppE hexp e) exps pats d
    (_, Value v) -> pure (False, makeAppE (hexp : v : exps))
    x -> do
      S.put originEnv
      pure x
patsMatch _ [] [] _ = pure (True, None)
patsMatch _ [] p _ = pure $ (False,
  Exception ("Number of arguments (0) and " ++
             "number of paterns (" ++ show (length p) ++ ") are not the same"))
patsMatch _ e p _ = pure $ (False,
  Exception ("Number of arguments (" ++ show (length e) ++ ") and " ++
             "number of paterns (" ++ show (length p) ++ ") are not the same"))-- TODO fix etared

toWHNF :: Exp -> S.StateT (Env Exp) IO (EitherNone Exp)
toWHNF (CompE stmts) = undefined -- TODO fix
toWHNF (ArithSeqE range) = undefined -- TODO fix
toWHNF (ListE (x : xs)) = pure $ Value (InfixE (Just x) (ConE '(:)) (Just (ListE xs)))
toWHNF e@(VarE x) = do
  env <- S.get
  if M.member x env
    then do
      e' <- toWHNF $ M.findWithDefault e x env
      case e' of
        Value v -> do
          env' <- S.get
          S.put $ M.insert x v env'
          pure $ e'
        x' -> pure $ x'
    else pure None
toWHNF exp = pure None

evaluateExp :: Q Exp -> Q [Dec] -> IO ()
evaluateExp qexp qdec = do
  e <- runQ qexp
  d <- runQ qdec
  process e d
  where
    process :: Exp -> [Dec] -> IO ()
    process e d = do
      S.runStateT (nextStep (Value e) d) M.empty
      return ()

    niceOutputPrint :: EitherNone Exp -> S.StateT (Env Exp) IO ()
    niceOutputPrint (Exception e) = fail e
    niceOutputPrint None = liftIO $ putStrLn "Return value is none"
    niceOutputPrint (Value e) = do
      env <- S.get
      liftIO $ putStrLn $ removeSpec $ pprint $ replaceVars e $ M.toList env

    nextStep :: EitherNone Exp -> [Dec] -> S.StateT (Env Exp) IO (EitherNone Exp)
    nextStep ene@(Value e) d = do
      x <- niceOutputPrint ene
      ene1 <- step e d
      nextStep ene1 d
    nextStep None _ = do
      liftIO $ putStrLn "No next steps"
      pure None
    nextStep (Exception e) _ = fail e


    removeSpec :: String -> String
    removeSpec =  unpack . flip (foldl (\s needle -> replace needle "" s)) ["GHC.Types.", "Ghc_step_eval.", "GHC.Num.", "GHC.Classes."] . pack

