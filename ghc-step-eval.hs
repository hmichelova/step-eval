{-# LANGUAGE TemplateHaskell, OverloadedStrings #-}
module Ghc_step_eval where

import FunDefs
import DataTypes

import Control.Monad
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Data.Maybe ( isNothing, fromJust )
import Prelude hiding ( id, const, take, map, filter, last, length, fst, snd, zip, zipWith )
import Data.Text (pack, unpack, replace)
import Language.Haskell.Interpreter
import qualified Data.Map as M
import qualified Control.Monad.Trans.State as S

$funcs

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

step :: Exp -> StateExp
step (VarE x) = do
  env <- S.get
  case getVar x env of
    Just exp -> do
      exp' <- step exp
      case exp' of
        Exception e -> pure $ Exception e
        None -> pure None
        Value v -> do
          env' <- S.get
          S.put $ insertVar x v env'
          pure $ Value $ (VarE x)
    Nothing -> pure None

step (ConE _) = pure None

step (LitE _) = pure None

step exp@(AppE exp1 exp2) = let (hexp : exps) = getSubExp exp1 ++ [exp2] in
  appExp hexp exps
  where
    getSubExp :: Exp -> [Exp]
    getSubExp (AppE exp1 exp2) = getSubExp exp1 ++ [exp2]
    getSubExp x                = [x] -- TODO check if correct

    appExp :: Exp -> [Exp] -> StateExp
    appExp hexp exps = do
      hexp' <- step hexp
      case hexp' of
        Exception e -> pure $ Exception e
        None -> applyExp hexp exps
        Value v -> pure $ makeAppE (v : exps)

    applyExp :: Exp -> [Exp] -> StateExp
    applyExp hexp@(VarE x) exps = do
      env <- S.get
      case getVar x env of
        Just v -> applyExp v exps
        Nothing -> do
          let decs = getDecs x False env
          processDecs hexp exps decs
    applyExp e@(InfixE _ _ _) [] = pure $ Exception $ "Function application `" ++ show (pprint e) ++ "` has no arguments"
    applyExp ie@(InfixE me1 exp me2) (e : exps) = do
      enexp' <- step exp
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
      nexp1' <- step hexp
      case nexp1' of
        Value exp1' -> pure $ makeAppE (exp1' : exps)
        x           -> pure x

    replaceAtIndex :: Int -> EitherNone Exp -> [Exp] -> [Exp]
    replaceAtIndex i (Value x) xs = take i xs ++ [x] ++ drop (i + 1) xs

step ie@(InfixE me1 exp me2) = do
  enexp' <- step exp
  case enexp' of
    Exception e -> pure $ Exception e
    None -> do
      eie1' <- stepMaybe me1
      case eie1' of
        Exception e -> pure $ Exception e
        None -> do
          list <- joinList ie
          case list of
            None -> do
              eie2' <- stepMaybe me2
              case eie2' of
                Exception e -> pure $ Exception e
                None -> if isNothing me1 || isNothing me2
                  then pure None
                  else do
                    env <- S.get
                    liftIO $ evalInterpreter $ replaceVars ie $ getVarList env
                Value e2' -> pure $ Value $ InfixE me1 exp (Just e2')
            x -> pure x
        Value e1' -> pure $ Value $ InfixE (Just e1') exp me2
    Value exp' -> pure $ Value $ InfixE me1 exp' me2 -- TODO fix?
  where
    joinList :: Exp -> StateExp
    joinList (VarE x) = do
      env <- S.get
      case getVar x env of
        Just e -> joinList e
        Nothing -> pure None
    joinList e@(ListE _) = pure $ Value e
    joinList (InfixE (Just e1) (ConE var) (Just e2)) = if var /= '(:) then pure None else do
      e2' <- joinList e2
      case e2' of
        Value (ListE xs) -> pure $ Value $ ListE (e1 : xs)
        x -> pure x
    joinList e = pure None

step (ParensE e) = do
  e' <- step e
  case e' of
    Value v -> pure $ Value $ ParensE v
    x -> pure x

step (LamE pats exp) = pure $ Exception "Lambda expressions are not supported yet"

step (TupE []) = pure None
step exp@(TupE (me : exps)) = do
  e' <- stepMaybe me
  case e' of
    None -> do
      exps' <- step (TupE exps)
      case exps' of
        Value (TupE xs) -> pure $ Value $ TupE $ me : xs
        Value _ -> pure $ Exception $ "Unsupported change of structure in tupple expression " ++ pprint exp
        x -> pure x
    Value v -> pure $ Value $ TupE $ (Just v) : exps
    x -> pure x

step (CondE b t f) = do
  b' <- step b
  case b' of
    Exception e -> pure $ Exception e
    None -> case b of
      ConE (Name (OccName n) _) -> pure $ if n == "True" then Value $ t else Value $ f
      otherwise -> pure $ Exception $ "Condition `" ++ pprint b ++ "` can't be evaluate to Bool expression"
    Value v -> pure $ Value $ CondE v t f

step (LetE decs exp) = pure $ Exception "Let expressions are not supported yet"

step (ListE []) = pure None
step exp@(ListE (e : exps)) = do
  e' <- step e
  case e' of
    None -> do
      exps' <- step (ListE exps)
      case exps' of
        Value (ListE xs) -> pure $ Value $ ListE $ e : xs
        Value _ -> pure $ Exception $ "Unsupported change of structure in list expression " ++ pprint exp
        x -> pure x
    Value v -> pure $ Value $ ListE $ v : exps
    x -> pure x
  
step exp = pure $ Exception $ "Unsupported format of expression: " ++ pprint exp

stepMaybe :: Maybe Exp -> StateExp
stepMaybe Nothing = pure $ None
stepMaybe (Just e) = step e

makeAppE :: [Exp] -> EitherNone Exp
makeAppE []  = Exception "Something went terribly wrong"
makeAppE [x] = Value x
makeAppE (x : y : xs) = makeAppE (AppE x y : xs)

patMatch' :: Pat -> Exp -> S.StateT Env IO (Bool, EitherNone Exp)
patMatch' p e = do
  rv1 <- patMatch p e
  case rv1 of
    (False, None) -> do
      env <- S.get
      let e' = replaceVars e (getVarList env)
      whnf <- toWHNFWithDefault e'
      case whnf of
        Value v -> do
          rv2 <- patMatch p v
          case rv2 of
            (False, None) -> do
              rv3 <- listJoin v
              case rv3 of
                None -> do
                  rv4 <- step e
                  pure (False, rv4)
                Value v' -> patMatch p v'
                x -> pure (False, x)
            x -> pure x
        x -> pure (False, x)
    x -> pure x
    
  where
    toWHNFWithDefault :: Exp -> StateExp
    toWHNFWithDefault e = do
      whnf <- toWHNF e
      case whnf of
        None -> pure $ Value e
        x -> pure $ x

    listJoin :: Exp -> StateExp
    listJoin e@(ListE _) = pure $ Value e
    listJoin e@(InfixE (Just e1) (ConE n) (Just e2)) = do
      if n == '(:)
        then do
          e2' <- listJoin e2
          case e2' of
            Value (ListE xs) -> pure $ Value $ ListE $ e1 : xs
            _ -> pure None
        else pure $ None
    listJoin e = pure $ None

patMatch :: Pat -> Exp -> S.StateT Env IO (Bool, EitherNone Exp)
patMatch (LitP lp) (LitE le) = pure (lp == le, None)
patMatch p@(LitP lp) _ = pure (False, None)
patMatch (VarP n) exp = do
  env <- S.get
  S.put $ insertVar n exp env
  pure (True, None)
patMatch (TupP ps) (TupE es) = if length ps /= length es
  then pure (False, None)
  else patMatchTup ps es
  where
    patMatchTup :: [Pat] -> [Maybe Exp] -> S.StateT Env IO (Bool, EitherNone Exp)
    patMatchTup [] [] = pure (True, None)
    patMatchTup (p : pats) (Just e : exps) = do
      rv <- patMatch p e
      case rv of
        (True, None) -> do
          rv1 <- patMatchTup pats exps
          case rv1 of
            (_, Value (TupE exps')) -> pure (False, Value (TupE (Just e : exps')))
            x -> pure x
        (_, Value v) -> pure (False, Value (TupE (Just v : exps)))
        x -> pure x
    patMatchTup (p : pats) (Nothing : exps) = pure (False, Exception "Missing argument in tuple")
    patMatchTup _ _ = pure (False, Exception "Something went wrong in tuples check")
patMatch pat@(TupP _) exp = pure (False, None)

patMatch pat@(UnboxedTupP _) _ =
  pure (False, Exception $ "Unboxed tupple pattern " ++ pprint pat ++ " is not supported")

patMatch pat@(UnboxedSumP _ _ _) _ =
  pure (False, Exception $ "Unboxed sum pattern " ++ pprint pat ++ " is not supported")

patMatch (ConP np _ []) (ConE ne) = pure (np == ne, None)
patMatch (ConP np _ []) (ListE []) = pure (np == '[], None)
patMatch (ConP np _ _) exp = pure (False, None) -- TODO AppE

patMatch (InfixP p1 np p2) (InfixE (Just e1) exp (Just e2)) = do
  rv <- patMatch' (ConP np [] []) exp -- TODO check
  case rv of
    (True, None) -> do
      rv1 <- patMatch' p1 e1
      case rv1 of
        (True, None) -> do
          rv2 <- patMatch' p2 e2
          case rv2 of
            (_, Value v) -> pure (False, Value (InfixE (Just e1) exp (Just v)))
            x -> pure x
        (_, Value v) -> pure (False, Value (InfixE (Just v) exp (Just e2)))
        x -> pure x
    (_, Value v) -> pure (False, Value (InfixE (Just e1) v (Just e2)))
    x -> pure x
patMatch (InfixP p1 np p2) exp = pure (False, None)-- TODO fix AppE

patMatch pat@(UInfixP _ _ _) _ =
  pure (False, Exception $ "UInfix pattern " ++ pprint pat ++ " is not supported")

patMatch (ParensP p) exp = patMatch p exp

patMatch pat@(TildeP _) _ =
  pure (False, Exception $ "Tilde pattern " ++ pprint pat ++ " is not supported")

patMatch pat@(BangP _) _ =
  pure (False, Exception $ "Bang pattern " ++ pprint pat ++ " is not supported")

patMatch (AsP n p) exp = do
  rv <- patMatch p exp
  case rv of
    (True, None) -> do
      env <- S.get
      S.put $ insertVar n exp env
      pure (True, None)
    x -> pure x

patMatch WildP _ = pure (True, None)
  
patMatch pat@(RecP _ _) _ =
  pure (False, Exception $ "Record pattern " ++ pprint pat ++ " is not supported")

patMatch (ListP ps) (ListE es) = if length ps /= length es
  then pure (False, None)
  else checkLists ps es
  where
    checkLists :: [Pat] -> [Exp] -> S.StateT Env IO (Bool, EitherNone Exp)
    checkLists [] [] = pure (True, None)
    checkLists (p : pats) (e : exps) = do
      rv <- patMatch' p e
      case rv of
        (True, None) -> do
          rv1 <- checkLists pats exps
          case rv1 of
            (_, Value (ListE exps')) -> pure (False, Value (ListE (e : exps')))
            x -> pure x
        (_, Value v) -> pure (False, Value (ListE (v : exps)))
        x -> pure x
    checkLists _ _ = pure (False, Exception "Something went wrong in lists check")
patMatch (ListP []) exp = patMatch (ConP '[] [] []) exp
patMatch (ListP (x : xs)) exp = patMatch (InfixP x '(:) (ListP xs)) exp

patMatch pat@(SigP _ _) _ =
  pure (False, Exception $ "Sig pattern " ++ pprint pat ++ " is not supported")

patMatch pat@(ViewP _ _) _ =
  pure (False, Exception $ "View pattern " ++ pprint pat ++ " is not supported")


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

processDecs :: Exp -> [Exp] -> [Dec] -> StateExp
processDecs hexp [exp1, exp2] [] = pure $ Value $ AppE (InfixE (Just exp1) hexp Nothing) exp2
processDecs hexp exps [] = let appE = makeAppE (hexp : exps) in
  case appE of
    Value v -> liftIO $ evalInterpreter v
    x -> pure x
processDecs hexp exps (FunD n [] : decs) = processDecs hexp exps decs
processDecs hexp exps (FunD n (Clause pats (NormalB e) whereDec : clauses) : decs) = do
  if length exps /= length pats
    then pure $ Exception "Wrong number of arguments in function ..."
    else do
      exp' <- patsMatch hexp exps pats
      changeOrContinue exp'
  where
    changeOrContinue :: (Bool, EitherNone Exp) -> StateExp
    changeOrContinue (_, Exception e) = pure $ Exception e
    changeOrContinue (False, None) = processDecs hexp exps ((FunD n clauses) : decs)
    changeOrContinue (True, None) = do
      env <- S.get
      S.put $ insertDec whereDec env
      pure $ Value e
    changeOrContinue (_, changedValue) = pure changedValue

processDecs hexp exps (FunD n (Clause pats (GuardedB gb) _ : clauses) : decs) = pure $ Exception "Guards are not supported"

patsMatch :: Exp -> [Exp] -> [Pat] -> S.StateT Env IO (Bool, EitherNone Exp)
patsMatch hexp (e : exps) (p : pats) = do
  originEnv <- S.get
  rv <- patMatch' p e
  case rv of
    (True, None) -> patsMatch (AppE hexp e) exps pats
    (_, Value v) -> pure (False, makeAppE (hexp : v : exps))
    x -> do
      S.put originEnv
      pure x
patsMatch _ [] [] = pure (True, None)
patsMatch _ [] p = pure $ (False,
  Exception ("Number of arguments (0) and " ++
             "number of paterns (" ++ show (length p) ++ ") are not the same"))
patsMatch _ e p = pure $ (False,
  Exception ("Number of arguments (" ++ show (length e) ++ ") and " ++
             "number of paterns (" ++ show (length p) ++ ") are not the same"))-- TODO fix etared

toWHNF :: Exp -> StateExp
toWHNF (CompE stmts) = undefined -- TODO fix
toWHNF (ArithSeqE range) = undefined -- TODO fix
toWHNF (ListE (x : xs)) = pure $ Value (InfixE (Just x) (ConE '(:)) (Just (ListE xs)))
toWHNF e@(VarE x) = do
  env <- S.get
  case getVar x env of
    Just v -> do
      e' <- toWHNF v
      case e' of
        Value v -> do
          env' <- S.get
          S.put $ insertVar x v env'
          pure $ e'
        x' -> pure $ x'
    Nothing -> pure None
toWHNF exp = pure None

evaluateExp :: Q Exp -> Q [Dec] -> IO ()
evaluateExp qexp qdec = do
  e <- runQ qexp
  d <- runQ qdec
  process e d
  where
    process :: Exp -> [Dec] -> IO ()
    process e d = do
      S.runStateT (nextStep (Value e)) $ setDec d emptyEnv
      return ()

    niceOutputPrint :: EitherNone Exp -> S.StateT Env IO ()
    niceOutputPrint (Exception e) = fail e
    niceOutputPrint None = liftIO $ putStrLn "Return value is none"
    niceOutputPrint (Value e) = do
      env <- S.get
      liftIO $ putStrLn $ removeSpec $ pprint $ replaceVars e $ getVarList env

    nextStep :: EitherNone Exp -> StateExp
    nextStep ene@(Value e) = do
      x <- niceOutputPrint ene
      ene1 <- step e
      nextStep ene1
    nextStep None = do
      liftIO $ putStrLn "Done"
      pure None
    nextStep (Exception e) = fail e


    removeSpec :: String -> String
    removeSpec =  unpack . flip (foldl (\s needle -> replace needle "" s)) ["GHC.Types.", "Ghc_step_eval.", "GHC.Num.", "GHC.Classes.", "GHC.List."] . pack

