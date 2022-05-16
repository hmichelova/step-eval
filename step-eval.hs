{-# LANGUAGE TemplateHaskell, OverloadedStrings #-}
module Step_eval (evaluateExp) where

import FunDefs
import DataTypes
import PatExpFuns

import Control.Monad
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Data.Maybe ( isNothing, fromJust )
import Data.List ( isSubsequenceOf )
import Prelude hiding ( id, const, take, map, filter, last, length, fst, snd, zip, zipWith, (&&), (||), not, takeWhile, dropWhile, enumFrom, enumFromThen, enumFromTo, enumFromThenTo )
import Data.Text (pack, unpack, replace)
import Language.Haskell.Interpreter
import qualified Control.Monad.Trans.State as S
import qualified Data.Map as M

$funcs

evalInterpreter :: Exp -> IOStepExp Exp
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
      t <- typeOf s
      evalByType t s

    evalByType "Integer" s = do
      r <- interpret s (as :: Integer)
      pure $ [| r |]
    evalByType "Int" s = do
      r <- interpret s (as :: Int)
      pure $ [| r |]
    evalByType "Num a => a" s = do
      r <- interpret s (as :: Integer)
      pure $ [| r |]
    evalByType "Bool" s = do
      r <- interpret s (as :: Bool)
      pure $ [| r |]
    evalByType "Char" s = do
      r <- interpret s (as :: Char)
      pure $ [| r |]
    evalByType "String" s = do
      r <- interpret s (as :: String)
      pure $ [| r |]
    evalByType "[Char]" s = do
      r <- interpret s (as :: String)
      pure $ [| r |]
    evalByType t s
      | isSubsequenceOf "->" t = error $ "Unexpected type \"" ++ t ++ "\" of expression \"" ++ s ++ "\" -- interpreter cannot evaluate functions"
      | isSubsequenceOf "=>" t = do
        r <- interpret s (as :: Integer)
        pure $ [| r |]
      | otherwise = error $ "Unexpected type \"" ++ t ++ "\" of expression \"" ++ s ++ "\""


    moduleList :: [ModuleName]
    moduleList = ["Prelude", "GHC.Num", "GHC.Base", "GHC.Types", "GHC.Classes", "GHC.List", "GHC.Err", "GHC.Enum"]

    replaces :: String -> String
    replaces = unpack . replace "GHC.Types." "" . pack

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
          S.put $ updateOrInsertVar x v env'
          pure $ Value $ (VarE x)
    Nothing -> do
      let decs = getDecs x False env
      if null decs
        then pure None
        else do
          exp' <- processDecs (VarE x) [] decs False
          case exp' of
            Value v -> do
              S.put $ insertVar x v env
              pure $ Value $ VarE x
            Exception e -> if e == "Wrong number of arguments in function " ++ pprint (VarE x)
              then pure None
              else pure exp'
            x -> pure exp'

step (ConE _) = pure None

step (LitE _) = pure None

step exp@(AppE exp1 exp2) = let (hexp : exps) = getSubExp exp1 ++ [exp2] in do
  hexp' <- step hexp
  case hexp' of
    Exception e -> pure $ Exception e
    None -> applyExp hexp exps
    Value v -> pure $ makeAppE (v : exps)
  where
    getSubExp :: Exp -> [Exp]
    getSubExp (AppE exp1 exp2) = getSubExp exp1 ++ [exp2]
    getSubExp x                = [x]

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
      pure $ substituteNothingInInfixE ie e >>= \ie' -> makeAppE (ie' : exps)
      where
        substituteNothingInInfixE :: Exp -> Exp -> StepExp Exp
        substituteNothingInInfixE ie@(InfixE me1 exp me2) e
          | isNothing me1 = Value $ InfixE (Just e) exp me2
          | isNothing me2 = Value $ InfixE me1 exp (Just e)
          | otherwise     = Exception $ "Infix expression `" ++ show (pprint ie) ++ "` is not operator section with argument " ++ show (pprint e)

    applyExp (LamE [] exp) [] = step exp
    applyExp e@(LamE [] _) exps = pure $ Exception $
      "There is no patterns in lambda expression " ++ pprint e ++
      " for arguments " ++ pprint exps
    applyExp e@(LamE _ _) [] = pure $ Exception $
      "There is no argument for lambda expression " ++ pprint e
    applyExp le@(LamE (pat : pats) exp) (e : exps) = do
      pm <- patMatch pat e
      case pm of
        PMatch rename -> let body = renameVars exp rename in
          pure $ makeAppE ((if null pats then body else LamE pats body) : exps)
        PNomatch -> pure $ Exception $
          "No pattern match for pattern " ++ pprint pat ++
          " for expression " ++ pprint e ++
          " in lambda expression " ++ pprint le
        PStep v -> pure $ makeAppE (le : v : exps)
        PException ex -> pure $ Exception ex

    applyExp hexp exps = do
      hexp' <- step hexp
      case hexp' of
        Value v -> pure $ makeAppE (v : exps)
        x -> pure x

    replaceAtIndex :: Int -> StepExp Exp -> [Exp] -> [Exp]
    replaceAtIndex i (Value x) xs = take i xs ++ [x] ++ drop (i + 1) xs

step ie@(InfixE me1@(Just e1) exp me2@(Just e2)) = do
  enexp' <- step exp
  case enexp' of
    Exception e -> pure $ Exception e
    None -> do
      e1' <- step e1
      case e1' of
        Exception e -> pure $ Exception e
        None -> do
          e2' <- step e2
          case e2' of
            Exception e -> pure $ Exception e
            None -> do
              list <- joinList ie
              case list of
                None -> evaluateInfixE ie
                x -> pure x
            Value exp2' -> pure $ Value $ InfixE me1 exp (Just exp2')
        Value exp1' -> pure $ Value $ InfixE (Just exp1') exp me2
    Value exp' -> pure $ Value $ InfixE me1 exp' me2
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
      liftIO $ evalInterpreter $ replaceVars ie (getVars env)
step ie@(InfixE _ _ _) = pure None

step (ParensE e) = do
  e' <- step e
  case e' of
    Value v -> pure $ Value $ ParensE v
    x -> pure x

step (LamE [] exp) = step exp
step (LamE pats exp) = pure None

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
      ConE (Name (OccName n) _) -> pure $ Value $ if n == "True" then t else f
      VarE x -> do
        env <- S.get
        case getVar x env of
          Just (ConE (Name (OccName n) _)) -> pure $ Value $ if n == "True" then t else f
          otherwise -> pure $ Exception $ "Condition `" ++ pprint b ++ "` can't be evaluate to Bool expression"
      otherwise -> pure $ Exception $ "Condition `" ++ pprint b ++ "` can't be evaluate to Bool expression"
    Value v -> pure $ Value $ CondE v t f

step (LetE decs exp) = do
  env <- S.get
  (rename, decs') <- renameDecs decs
  S.put $ insertDec decs' env
  pure $ Value $ renameVars exp rename

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

step exp@(ArithSeqE (FromR fr)) = pure $ Value $ AppE (VarE 'enumFrom) fr
step exp@(ArithSeqE (FromThenR fr th)) = pure $ Value $ AppE (AppE (VarE 'enumFromThen) fr) th
step exp@(ArithSeqE (FromToR fr to)) = pure $ Value $ AppE (AppE (VarE 'enumFromTo) fr) to
step exp@(ArithSeqE (FromThenToR fr th to)) =  pure $ Value $
  AppE (AppE (AppE (VarE 'enumFromThenTo) fr)
             th)
       to
step exp = pure $ Exception $ "Unsupported format of expression: " ++ pprint exp

stepMaybe :: Maybe Exp -> StateExp
stepMaybe Nothing = pure $ None
stepMaybe (Just e) = step e

patsMatch :: Exp -> [Exp] -> [Pat] -> S.StateT Env IO PatternMatch
patsMatch hexp (e : exps) (p : pats) = do
  originEnv <- S.get
  rv <- patMatch p e
  case rv of
    PMatch rename -> do
      rv1 <- patsMatch (AppE hexp e) exps pats
      case rv1 of
        PMatch rename1 -> pure $ PMatch $ M.union rename rename1
        x -> pure x
    PStep v -> pure $ matched $ makeAppE (hexp : v : exps)
    x -> do
      S.put originEnv
      pure x
patsMatch _ [] [] = pure $ PMatch M.empty
patsMatch _ [] p = pure $ PException $
  "Number of arguments (0) and " ++
  "number of paterns (" ++ show (length p) ++ ") are not the same"
patsMatch _ e p = pure $ PException $
  "Number of arguments (" ++ show (length e) ++ ") and " ++
  "number of paterns (" ++ show (length p) ++ ") are not the same"

patMatch :: Pat -> Exp -> S.StateT Env IO PatternMatch
patMatch pat exp = patMatchWHNF (toWHNFP pat) (toWHNFE exp) exp

patMatchWHNF :: Pat -> Exp -> Exp -> S.StateT Env IO PatternMatch
patMatchWHNF (LitP lp) (LitE le) _ = pure $ if lp == le then PMatch M.empty else PNomatch
patMatchWHNF p@(LitP _) exp orig = patMatch' p exp orig

patMatchWHNF (VarP np) e@(VarE ne) _ = if np == ne then pure (PMatch M.empty) else do
  env <- S.get
  name <- liftIO $ newName $ getName np
  S.put $ insertVar name e env
  pure $ PMatch $ M.fromList [(np, name)]
patMatchWHNF (VarP n) exp _ = do
  env <- S.get
  name <- liftIO $ newName $ getName n
  S.put $ insertVar name exp env
  pure $ PMatch $ M.fromList [(n, name)]

patMatchWHNF (TupP ps) (TupE es) _ = if length ps /= length es
  then pure PNomatch
  else patMatchWHNFTup ps es
  where
    patMatchWHNFTup :: [Pat] -> [Maybe Exp] -> S.StateT Env IO PatternMatch
    patMatchWHNFTup [] [] = pure $ PMatch M.empty
    patMatchWHNFTup (p : pats) (Just e : exps) = do
      rv <- patMatch p e
      case rv of
        PMatch rename -> do
          rv1 <- patMatchWHNFTup pats exps
          case rv1 of
            PMatch rename1 -> pure $ PMatch $ M.union rename rename1
            PStep (TupE exps') -> pure $ PStep $ TupE $ Just e : exps'
            x -> pure x
        PStep v -> pure $ PStep $ TupE $ Just v : exps
        x -> pure x
    patMatchWHNFTup (p : pats) (Nothing : exps) = pure $ PException "Missing argument in tuple"
    patMatchWHNFTup _ _ = pure $ PException "Something went wrong in tuples check"

patMatchWHNF p@(TupP _) exp orig = patMatch' p exp orig

patMatchWHNF pat@(UnboxedTupP _) _ _ =
  pure $ PException $ "Unboxed tupple pattern " ++ pprint pat ++ " is not supported"

patMatchWHNF pat@(UnboxedSumP _ _ _) _ _ =
  pure $ PException $ "Unboxed sum pattern " ++ pprint pat ++ " is not supported"

patMatchWHNF (ConP np _ []) (ConE ne) _ = pure $ if np == ne then PMatch M.empty else PNomatch
patMatchWHNF p@(ConP np _ []) exp@(InfixE me1 (ConE n) me2) orig = if n == '(:) && np == '[]
  then pure PNomatch
  else patMatch' p exp orig
patMatchWHNF p@(ConP np _ _) exp orig = patMatch' p exp orig

patMatchWHNF (InfixP p1 np p2) (InfixE (Just e1) exp (Just e2)) _ = do
  rv <- patMatch (ConP np [] []) exp
  case rv of
    PMatch rename -> do
      rv1 <- patMatch p1 e1
      case rv1 of
        PMatch rename1 -> do
          rv2 <- patMatch p2 e2
          case rv2 of
            PMatch rename2 -> pure $ PMatch $ M.union rename $ M.union rename1 rename2
            PStep v -> pure $ PStep $ InfixE (Just e1) exp (Just v)
            x -> pure x
        PStep v -> pure $ PStep $ InfixE (Just v) exp (Just e2)
        x -> pure x
    PStep v -> pure $ PStep $ InfixE (Just e1) v (Just e2)
    x -> pure x
patMatchWHNF p@(InfixP _ np _) exp@(ConE ne) orig = if np == '(:) && ne == '[]
  then pure PNomatch
  else patMatch' p exp orig
patMatchWHNF p@(InfixP _ _ _) exp orig = patMatch' p exp orig

patMatchWHNF pat@(UInfixP _ _ _) _ _ =
  pure $ PException $ "UInfix pattern " ++ pprint pat ++ " is not supported"

patMatchWHNF (ParensP p) exp _ = patMatch p exp

patMatchWHNF pat@(TildeP _) _ _ =
  pure $ PException $ "Tilde pattern " ++ pprint pat ++ " is not supported"

patMatchWHNF pat@(BangP _) _ _ =
  pure $ PException $ "Bang pattern " ++ pprint pat ++ " is not supported"

patMatchWHNF (AsP n p) exp _ = do
  rv <- patMatch p exp
  case rv of
    PMatch rename -> do
      env <- S.get
      name <- liftIO $ newName $ getName n
      S.put $ insertVar name (replaceVars exp (getVars env)) env
      pure $ PMatch $ M.union rename $ M.fromList [(n, name)]
    x -> pure x

patMatchWHNF WildP _ _ = pure $ PMatch M.empty
  
patMatchWHNF pat@(RecP _ _) _ _ =
  pure $ PException $ "Record pattern " ++ pprint pat ++ " is not supported"
patMatchWHNF pat@(SigP _ _) _ _ =
  pure $ PException $ "Sig pattern " ++ pprint pat ++ " is not supported"

patMatchWHNF pat@(ViewP _ _) _ _ =
  pure $ PException $ "View pattern " ++ pprint pat ++ " is not supported"


patMatch' :: Pat -> Exp -> Exp -> S.StateT Env IO PatternMatch
patMatch' p exp orig = do
  env <- S.get
  let expReplaced = replaceVars exp (getVars env)
  if expReplaced /= exp
    then patMatch p $ toWHNFE expReplaced
    else do
      orig' <- step orig
      pure $ matched orig'

processDecs :: Exp -> [Exp] -> [Dec] -> Bool -> StateExp
processDecs hexp [exp1, exp2] [] False = pure $ Value $ AppE (InfixE (Just exp1) hexp Nothing) exp2
processDecs hexp exps [] _ = do
  let appE = makeAppE (hexp : exps)
  env <- S.get
  case appE of
    Value v -> liftIO $ evalInterpreter $ replaceVars v (getVars env)
    x -> pure x
processDecs hexp exps (FunD n [] : decs) b = processDecs hexp exps decs b
processDecs hexp exps (FunD n (Clause pats (NormalB e) whereDec : clauses) : decs) b = do
  if length exps /= length pats
    then pure $ Exception $ "Wrong number of arguments in function " ++ pprint hexp
    else do
      exp' <- patsMatch hexp exps pats
      changeOrContinue exp'
  where
    changeOrContinue :: PatternMatch -> StateExp
    changeOrContinue PNomatch = processDecs hexp exps ((FunD n clauses) : decs) b
    changeOrContinue (PMatch rename) = do
      env <- S.get
      S.put $ insertDec (replaceDecs whereDec rename []) env
      pure $ Value $ renameVars e rename
    changeOrContinue (PStep v) = pure $ Value v
    changeOrContinue (PException e) = pure $ Exception e

processDecs hexp exps (FunD n (Clause pats (GuardedB gb) _ : clauses) : decs) _ = pure $ Exception "Guards are not supported"

processDecs hexp@(VarE x) [] (ValD pat (NormalB e) whereDec : decs) b =
  if notElem x (getNamesFromPats [pat])
    then processDecs hexp [] decs b
    else do
      m <- patMatch pat e
      changeOrContinue m
  where
    changeOrContinue :: PatternMatch -> StateExp
    changeOrContinue PNomatch = processDecs hexp [] decs b
    changeOrContinue (PMatch rename) = do
      env <- S.get
      S.put $ insertDec (replaceDecs whereDec rename []) env
      env' <- S.get
      case M.lookup x rename of
        Just x' -> do
          case getVar x' env' of
            Just v -> pure $ Value $ renameVars v rename
            Nothing -> pure $ Exception $ "Variable " ++ pprint x ++ " is missing"
        Nothing -> pure $ Exception $ "Variable " ++ pprint x ++ " is missing"
    changeOrContinue (PStep v) = do
      m <- patMatch pat e
      changeOrContinue m
    changeOrContinue (PException e) = pure $ Exception e

processDecs hexp exps (ValD pat (GuardedB gb) whereDecs : decs) _ = pure $ Exception "Guards are not supported"

processDecs hexp exps (ValD _ _ _ : decs) b = processDecs hexp exps decs b

renameDecs :: [Dec] -> S.StateT Env IO (Dictionary Name, [Dec])
renameDecs [] = pure (M.empty, [])
renameDecs (dec : decs) = do
  (rename, dec') <- renameDec dec
  (rename', decs') <- renameDecs decs
  pure (M.union rename rename', replaceDec dec' rename' [] : replaceDecs decs' rename [])

  where
    renameDec :: Dec -> S.StateT Env IO (Dictionary Name, Dec)
    renameDec (FunD name clauses) = do
      n <- liftIO $ newName $ getName name
      let rename = M.singleton name n
      pure (rename, FunD n (replaceClauses clauses rename []))
    renameDec (ValD pat body whereDec) = do
      rename <- renamePat pat
      let whereDec' = replaceDecs whereDec rename []
      (rename', whereDec'') <- renameDecs whereDec'
      pure (rename, ValD (replacePat pat rename)
                         (replaceBody body (M.union rename' rename) [])
                         whereDec''
           )
    renameDec dec = pure (M.empty, dec)

    renamePat :: Pat -> S.StateT Env IO (Dictionary Name)
    renamePat (LitP _) = pure M.empty
    renamePat (VarP n) = do
      n' <- liftIO $ newName $ getName n
      pure $ M.singleton n n'
    renamePat (TupP []) = pure M.empty
    renamePat (TupP (x : xs)) = do
      rename' <- renamePat x
      rename'' <- renamePat $ TupP xs
      pure $ M.union rename' rename''
    renamePat (InfixP p1 _ p2) = do
      rename' <- renamePat p1
      rename'' <- renamePat p2
      pure $ M.union rename' rename''
    renamePat (ParensP p) = renamePat p
    renamePat (AsP n p2) = do
      n' <- liftIO $ newName $ getName n
      rename' <- renamePat p2
      pure $ M.union (M.singleton n n') rename'
    renamePat (ListP []) = pure M.empty
    renamePat (ListP (x : xs)) = do
      rename' <- renamePat x
      rename'' <- renamePat $ ListP xs
      pure $ M.union rename' rename''
    renamePat _ = pure M.empty

evaluateExp :: Code Q a -> IO ()
evaluateExp = flip evaluateExp' funcs . examineCode

evaluateExp' :: Q (TExp a) -> Q [Dec] -> IO ()
evaluateExp' tqexp qdec = do
  te <- runQ tqexp
  d <- runQ qdec
  process (unType te) d
  where
    process :: Exp -> [Dec] -> IO ()
    process e d = do
      S.runStateT (nextStep (Value e) False) $ setDefaultDec d emptyEnv
      return ()

    niceOutputPrint :: StepExp Exp -> S.StateT Env IO ()
    niceOutputPrint (Exception e) = fail e
    niceOutputPrint None = liftIO $ putStrLn "Return value is none"
    niceOutputPrint (Value e) = do
      env <- S.get
      liftIO $ putStrLn $ removeSpec $ pprint $ replaceVars e (getVars env)

    nextStep :: StepExp Exp -> Bool -> StateExp
    nextStep ene@(Value e) b = do
      niceOutputPrint ene
      liftIO $ putStrLn $ ""
      if b
        then do
          ene1 <- step e
          nextStep ene1 b
        else askAndStep
      where
        askAndStep = do
          liftIO $ putStr $ "Next action [N,a,q,h]? "
          s <- liftIO getLine
          let s' = if null s then "n" else s
          case head s' of
            'h' -> do
              liftIO $ putStrLn "ghc-step-eval help: "
              liftIO $ putStrLn "  n: print next step and ask again"
              liftIO $ putStrLn "  a: print all following steps"
              liftIO $ putStrLn "  q: quit the evaluation"
              liftIO $ putStrLn "  h: print help"
              liftIO $ putStrLn $ ""
              askAndStep
            'a' -> do
              ene1 <- step e
              nextStep ene1 True
            'q' -> pure None
            _   -> do
              ene1 <- step e
              nextStep ene1 False
    nextStep None _ = do
      liftIO $ putStrLn "Expression is fully evaluated."
      pure None
    nextStep (Exception e) _ = fail e


    removeSpec :: String -> String
    removeSpec =  unpack . flip (foldl (\s needle -> replace needle "" s)) ["GHC.Types.", "Step_eval.", "GHC.Num.", "GHC.Classes.", "GHC.List.", "GHC.Err.", "GHC.Enum.", "GHC.Base."] . pack

