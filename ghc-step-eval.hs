{-# LANGUAGE TemplateHaskell, OverloadedStrings #-}
module Ghc_step_eval where

import FunDefs
import DataTypes

import Control.Monad
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Data.Maybe ( isNothing, fromJust )
import Prelude hiding ( id, const, take, map, filter, last, length, fst, snd, zip, zipWith, (&&), (||), not )
import Data.Text (pack, unpack, replace)
import Language.Haskell.Interpreter
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
    moduleList = ["Prelude", "GHC.Num", "GHC.Base", "GHC.Types", "GHC.Classes", "GHC.List", "GHC.Err"]

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
          processDecs hexp exps decs False
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
          eie2' <- stepMaybe me2
          case eie2' of
            Exception e -> pure $ Exception e
            None -> if isNothing me1 || isNothing me2
              then pure None
              else do
                list <- joinList ie
                case list of
                  None -> evaluateInfixE ie
                  x -> pure x
            Value e2' -> pure $ Value $ InfixE me1 exp (Just e2')
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
    joinList (ConE n) = pure $ if n == '[] then Value $ ListE [] else None
    joinList (InfixE (Just e1) (ConE var) (Just e2)) = if var /= '(:) then pure None else do
      e2' <- joinList e2
      case e2' of
        Value (ListE xs) -> pure $ Value $ ListE (e1 : xs)
        x -> pure x
    joinList e = pure None

    evaluateInfixE :: Exp -> StateExp
    evaluateInfixE (InfixE (Just e1) (VarE x) (Just e2)) = do
      env <- S.get
      let decs = getDecs x False env
      processDecs exp [e1, e2] decs True
    evaluateInfixE ei = do
      env <- S.get
      liftIO $ evalInterpreter $ replaceVars ie (getVars env) id

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

patMatch :: Pat -> Exp -> S.StateT Env IO PatternMatch
patMatch (LitP lp) (LitE le) = pure $ if lp == le then PMatch [] else PNomatch
patMatch p@(LitP _) exp = patMatch' p exp

patMatch (VarP np) e@(VarE ne) = if np == ne then pure (PMatch []) else do
  env <- S.get
  name <- liftIO $ newName $ getName np
  S.put $ insertVar name e env
  pure $ PMatch $ [(np, name)]
patMatch (VarP n) exp = do
  env <- S.get
  name <- liftIO $ newName $ getName n
  S.put $ insertVar name exp env
  pure $ PMatch $ [(n, name)]

patMatch (TupP ps) (TupE es) = if length ps /= length es
  then pure PNomatch
  else patMatchTup ps es
  where
    patMatchTup :: [Pat] -> [Maybe Exp] -> S.StateT Env IO PatternMatch
    patMatchTup [] [] = pure $ PMatch []
    patMatchTup (p : pats) (Just e : exps) = do
      rv <- patMatch p e
      case rv of
        PMatch rename -> do
          rv1 <- patMatchTup pats exps
          case rv1 of
            PMatch rename1 -> pure $ PMatch $ rename ++ rename1
            PStep (TupE exps') -> pure $ PStep $ TupE $ Just e : exps'
            x -> pure x
        PStep v -> pure $ PStep $ TupE $ Just v : exps
        x -> pure x
    patMatchTup (p : pats) (Nothing : exps) = pure $ PException "Missing argument in tuple"
    patMatchTup _ _ = pure $ PException "Something went wrong in tuples check"

patMatch p@(TupP _) exp = patMatch' p exp

patMatch pat@(UnboxedTupP _) _ =
  pure $ PException $ "Unboxed tupple pattern " ++ pprint pat ++ " is not supported"

patMatch pat@(UnboxedSumP _ _ _) _ =
  pure $ PException $ "Unboxed sum pattern " ++ pprint pat ++ " is not supported"

-- TODO add (ConP np _ (x : xs)) - for user defined data types
patMatch (ConP np _ []) (ConE ne) = pure $ if np == ne then PMatch [] else PNomatch
patMatch (ConP np _ []) (ListE []) = pure $ if np == '[] then PMatch [] else PNomatch
patMatch (ConP np _ []) (ListE (_ : _)) = pure PNomatch
patMatch p@(ConP np _ []) exp@(InfixE me1 (ConE n) me2) = if n == '(:) && np == '[]
  then pure PNomatch
  else patMatch' p exp
patMatch p@(ConP np _ _) exp = patMatch' p exp

patMatch (InfixP p1 np p2) (InfixE (Just e1) exp (Just e2)) = do
  rv <- patMatch (ConP np [] []) exp
  case rv of
    PMatch rename -> do
      rv1 <- patMatch p1 e1
      case rv1 of
        PMatch rename1 -> do
          rv2 <- patMatch p2 e2
          case rv2 of
            PMatch rename2 -> pure $ PMatch $ rename ++ rename1 ++ rename2
            PStep v -> pure $ PStep $ InfixE (Just e1) exp (Just v)
            x -> pure x
        PStep v -> pure $ PStep $ InfixE (Just v) exp (Just e2)
        x -> pure x
    PStep v -> pure $ PStep $ InfixE (Just e1) v (Just e2)
    x -> pure x
patMatch p@(InfixP _ np _) exp@(ConE ne) = if np == '(:) && ne == '[]
  then pure PNomatch
  else patMatch' p exp
patMatch p@(InfixP _ np _) exp@(ListE []) = if np == '(:)
  then pure PNomatch
  else pure $ PException $ "Try to match value " ++ pprint exp ++ " to pattern " ++ pprint p
patMatch p@(InfixP _ _ _) exp = patMatch' p exp

patMatch pat@(UInfixP _ _ _) _ =
  pure $ PException $ "UInfix pattern " ++ pprint pat ++ " is not supported"

patMatch (ParensP p) exp = patMatch p exp

patMatch pat@(TildeP _) _ =
  pure $ PException $ "Tilde pattern " ++ pprint pat ++ " is not supported"

patMatch pat@(BangP _) _ =
  pure $ PException $ "Bang pattern " ++ pprint pat ++ " is not supported"

patMatch (AsP n p) exp = do
  rv <- patMatch p exp
  case rv of
    PMatch rename -> do
      env <- S.get
      name <- liftIO $ newName $ getName n
      S.put $ insertVar name (replaceVars exp (getVars env) id) env -- TODO rewrite
      pure $ PMatch $ rename ++ [(n, name)]
    x -> pure x

patMatch WildP _ = pure $ PMatch []
  
patMatch pat@(RecP _ _) _ =
  pure $ PException $ "Record pattern " ++ pprint pat ++ " is not supported"

patMatch (ListP ps) (ListE es) = if length ps /= length es
  then pure PNomatch
  else checkLists ps es
  where
    checkLists :: [Pat] -> [Exp] -> S.StateT Env IO PatternMatch
    checkLists [] [] = pure $ PMatch []
    checkLists (p : pats) (e : exps) = do
      rv <- patMatch p e
      case rv of
        PMatch rename -> do
          rv1 <- checkLists pats exps
          case rv1 of
            PMatch rename1 -> pure $ PMatch $ rename ++ rename1
            PStep (ListE exps') -> pure $ PStep $ ListE $ e : exps'
            x -> pure x
        PStep v -> pure $ PStep $ ListE $ v : exps
        x -> pure x
    checkLists _ _ = pure $ PException "Something went wrong in lists check"
patMatch (ListP []) exp = patMatch (ConP '[] [] []) exp
patMatch (ListP (x : xs)) exp = patMatch (InfixP x '(:) (ListP xs)) exp

patMatch pat@(SigP _ _) _ =
  pure $ PException $ "Sig pattern " ++ pprint pat ++ " is not supported"

patMatch pat@(ViewP _ _) _ =
  pure $ PException $ "View pattern " ++ pprint pat ++ " is not supported"


patMatch' :: Pat -> Exp -> S.StateT Env IO PatternMatch
patMatch' p exp = do
  env <- S.get
  let expReplaced = replaceVars exp (getVars env) id
  if expReplaced /= exp
    then patMatch p expReplaced
    else do
      expWHNF <- toWHNF exp
      case expWHNF of
        None -> do
          exp' <- step exp
          pure $ matched exp'
        Value v -> patMatch p v
        x -> pure $ matched x

matched :: EitherNone Exp -> PatternMatch
matched None = PNomatch
matched (Value v) = PStep v
matched (Exception e) = PException e

replaceVars :: Exp -> Dictionary a -> (a -> Exp) -> Exp
replaceVars exp rename f = foldl (\exp (n, e) -> replaceVar exp n e f) exp rename

replaceVar :: Exp -> Name -> a -> (a -> Exp) -> Exp
replaceVar exp@(VarE name) n e f = if name == n then f e else exp
replaceVar exp@(ConE _) _ _ _ = exp
replaceVar exp@(LitE _) _ _ _ = exp
replaceVar (AppE e1 e2) n e f = AppE (replaceVar e1 n e f) (replaceVar e2 n e f)
replaceVar (InfixE me1 exp me2) n e f =
  InfixE (maybe Nothing (\e1 -> Just (replaceVar e1 n e f)) me1)
         (replaceVar exp n e f)
         (maybe Nothing (\e2 -> Just (replaceVar e2 n e f)) me2)
replaceVar (ParensE exp) n e f = ParensE (replaceVar exp n e f)
replaceVar (LamE pats exp) n e f = undefined -- TODO
replaceVar (TupE mexps) n e f =
  TupE $ map (maybe Nothing (\e' -> Just (replaceVar e' n e f))) mexps
replaceVar (CondE b t f) n e fun =
  CondE (replaceVar b n e fun) (replaceVar t n e fun) (replaceVar f n e fun)
replaceVar (ListE xs) n e f = ListE $ map (\exp -> replaceVar exp n e f) xs
replaceVar exp _ _ _ = exp -- TODO

getName :: Name -> String
getName (Name (OccName n) _) = n

processDecs :: Exp -> [Exp] -> [Dec] -> Bool -> StateExp
processDecs hexp [exp1, exp2] [] False = pure $ Value $ AppE (InfixE (Just exp1) hexp Nothing) exp2
processDecs hexp exps [] _ = do
  let appE = makeAppE (hexp : exps)
  env <- S.get
  case appE of
    Value v -> liftIO $ evalInterpreter $ replaceVars v (getVars env) id
    x -> pure x
processDecs hexp exps (FunD n [] : decs) b = processDecs hexp exps decs b
processDecs hexp exps (FunD n (Clause pats (NormalB e) whereDec : clauses) : decs) b = do
  if length exps /= length pats
    then pure $ Exception "Wrong number of arguments in function ..."
    else do
      exp' <- patsMatch hexp exps pats
      changeOrContinue exp'
  where
    changeOrContinue :: PatternMatch -> StateExp
    changeOrContinue PNomatch = processDecs hexp exps ((FunD n clauses) : decs) b
    changeOrContinue (PMatch rename) = do
      env <- S.get
      S.put $ insertDec whereDec env -- TODO rename by rename
      pure $ Value $ replaceVars e rename VarE
    changeOrContinue (PStep v) = pure $ Value v
    changeOrContinue (PException e) = pure $ Exception e

processDecs hexp exps (FunD n (Clause pats (GuardedB gb) _ : clauses) : decs) _ = pure $ Exception "Guards are not supported"

patsMatch :: Exp -> [Exp] -> [Pat] -> S.StateT Env IO PatternMatch
patsMatch hexp (e : exps) (p : pats) = do
  originEnv <- S.get
  rv <- patMatch p e
  case rv of
    PMatch rename -> do
      rv1 <- patsMatch (AppE hexp e) exps pats
      case rv1 of
        PMatch rename1 -> pure $ PMatch $ rename ++ rename1
        x -> pure x
    PStep v -> pure $ matched $ makeAppE (hexp : v : exps)
    x -> do
      S.put originEnv
      pure x
patsMatch _ [] [] = pure $ PMatch []
patsMatch _ [] p = pure $ PException $
  "Number of arguments (0) and " ++
  "number of paterns (" ++ show (length p) ++ ") are not the same"
patsMatch _ e p = pure $ PException $
  "Number of arguments (" ++ show (length e) ++ ") and " ++
  "number of paterns (" ++ show (length p) ++ ") are not the same" -- TODO fix etared

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

evaluateExp :: Q Exp -> IO ()
evaluateExp = flip evaluateExp' funcs

evaluateExp' :: Q Exp -> Q [Dec] -> IO ()
evaluateExp' qexp qdec = do
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
      liftIO $ putStrLn $ removeSpec $ pprint $ replaceVars e (getVars env) id

    nextStep :: EitherNone Exp -> StateExp
    nextStep ene@(Value e) = do
      niceOutputPrint ene
      ene1 <- step e
      nextStep ene1
    nextStep None = do
      liftIO $ putStrLn "Done"
      pure None
    nextStep (Exception e) = fail e


    removeSpec :: String -> String
    removeSpec =  unpack . flip (foldl (\s needle -> replace needle "" s)) ["GHC.Types.", "Ghc_step_eval.", "GHC.Num.", "GHC.Classes.", "GHC.List.", "GHC.Err."] . pack

