module PatExpFuns where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import qualified Data.Map as M

import DataTypes

getDecs :: Name -> Bool -> Env -> [Dec]
getDecs n@(Name (OccName on) _) sign (_, c, d) = filter sameName c ++ filter sameOccName d
  where
    sameName :: Dec -> Bool
    sameName (SigD name _) = sign && n == name
    sameName (FunD name _) = n == name
    sameName (ValD pat _ _) = any (n ==) $ getNamesFromPat pat
    sameName _             = False

    sameOccName :: Dec -> Bool
    sameOccName (SigD (Name (OccName name) _) _) = sign && on == name
    sameOccName (FunD (Name (OccName name) _) _) = on == name
    sameOccName (ValD pat _ _) = any (\(Name (OccName name) _) -> on == name) $ getNamesFromPat pat
    sameOccName _             = False

isNone :: EitherNone Exp -> Bool
isNone None = True
isNone _    = False

fromValue :: EitherNone Exp -> Exp
fromValue (Value exp) = exp
fromValue x           = error ("Function `fromValue` is used for: " ++ show x)

makeAppE :: [Exp] -> EitherNone Exp
makeAppE []  = Exception "Something went terribly wrong"
makeAppE [x] = Value x
makeAppE (x : y : xs) = makeAppE (AppE x y : xs)

matched :: EitherNone Exp -> PatternMatch
matched None = PNomatch
matched (Value v) = PStep v
matched (Exception e) = PException e

replaceDecs :: [Dec] -> Dictionary Name -> [Name] -> [Dec]
replaceDecs decs rename notR = map (\dec -> replaceDec dec rename notR) decs

replaceDec :: Dec -> Dictionary Name -> [Name] -> Dec
replaceDec (FunD name clauses) rename notR =
  FunD name $ replaceClauses clauses rename notR
replaceDec (ValD pat body whereDec) rename notR =
  ValD pat (replaceBody body rename (getNamesFromPats [pat] ++ notR))
           (replaceDecs whereDec rename (getNamesFromPats [pat] ++ notR))
replaceDec dec _ _ = dec

replaceClauses :: [Clause] -> Dictionary Name -> [Name] -> [Clause]
replaceClauses clauses rename notR = map (\c -> replaceClause c rename notR) clauses

replaceClause :: Clause -> Dictionary Name -> [Name] -> Clause
replaceClause (Clause pats body decs) rename notR =
  Clause pats (replaceBody body rename (getNamesFromPats pats ++ notR))
              (replaceDecs decs rename (getNamesFromPats pats ++ notR))

replaceBody :: Body -> Dictionary Name -> [Name] -> Body
replaceBody (NormalB exp) rename notR = NormalB $ replaceVar exp rename VarE notR
replaceBody b _ _ = b -- TODO guards

replacePat :: Pat -> Dictionary Name -> Pat
replacePat (VarP n) d = VarP $ M.findWithDefault n n d
replacePat (TupP ps) d = TupP $ map (flip replacePat d) ps
replacePat (UnboxedTupP ps) d = UnboxedTupP $ map (flip replacePat d) ps
replacePat (UnboxedSumP p _ _) d = undefined
replacePat (ConP n t ps) d = ConP n t $ map (flip replacePat d) ps
replacePat (InfixP p1 n p2) d = InfixP (replacePat p1 d) n $ replacePat p2 d
replacePat (UInfixP p1 n p2) d = UInfixP (replacePat p1 d) n $ replacePat p2 d
replacePat (ParensP p) d = ParensP $ replacePat p d
replacePat (TildeP p) d = TildeP $ replacePat p d
replacePat (BangP p) d = BangP $ replacePat p d
replacePat (AsP n p) d = AsP (M.findWithDefault n n d) $ replacePat p d
replacePat (RecP _ _) d = undefined
replacePat (ListP ps) d = ListP $ map (flip replacePat d) ps
replacePat (SigP p t) d = SigP (replacePat p d) t
replacePat (ViewP _ _) d = undefined

replaceVars :: Exp -> Dictionary Exp -> Exp
replaceVars exp rename = replaceVar exp rename id []

replaceVar :: Exp -> Dictionary a -> (a -> Exp) -> [Name] -> Exp
replaceVar exp@(VarE name) d f notR = if elem name notR then exp
  else case M.lookup name d of
    Nothing -> exp
    Just a -> replaceVar (f a) d f notR
replaceVar exp@(ConE _) _ _ _ = exp
replaceVar exp@(LitE _) _ _ _ = exp
replaceVar (AppE e1 e2) d f notR = AppE (replaceVar e1 d f notR) (replaceVar e2 d f notR)
replaceVar (InfixE me1 exp me2) d f notR =
  InfixE (maybe Nothing (\e1 -> Just (replaceVar e1 d f notR)) me1)
         (replaceVar exp d f notR)
         (maybe Nothing (\e2 -> Just (replaceVar e2 d f notR)) me2)
replaceVar (ParensE exp) d f notR = ParensE (replaceVar exp d f notR)
replaceVar le@(LamE pats exp) d f notR =
  LamE pats $ replaceVar exp d f (getNamesFromPats pats ++ notR)
replaceVar (TupE mexps) d f notR =
  TupE $ map (maybe Nothing (\e' -> Just (replaceVar e' d f notR))) mexps
replaceVar (CondE b t f) d fun notR =
  CondE (replaceVar b d fun notR) (replaceVar t d fun notR) (replaceVar f d fun notR)
replaceVar (LetE decs exp) d fun notR =
  LetE decs (replaceVar exp d fun (notR ++ getPats decs))
  where
    getPats :: [Dec] -> [Name]
    getPats = concatMap getPats'

    getPats' :: Dec -> [Name]
    getPats' (FunD n _) = [n]
    getPats' (ValD p _ _) = getNamesFromPat p
replaceVar (ListE xs) d f notR = ListE $ map (\exp -> replaceVar exp d f notR) xs
replaceVar (ArithSeqE range) d f notR = ArithSeqE $ replaceVarRange range
  where
    replaceVarRange :: Range -> Range
    replaceVarRange (FromR fr) = FromR $ replaceVar fr d f notR
    replaceVarRange (FromThenR fr th) = FromThenR (replaceVar fr d f notR) $ replaceVar th d f notR
    replaceVarRange (FromToR fr to) = FromToR (replaceVar fr d f notR) $ replaceVar to d f notR
    replaceVarRange (FromThenToR fr th to) = FromThenToR (replaceVar fr d f notR)
                                                         (replaceVar th d f notR)
                                                         (replaceVar to d f notR)
    
replaceVar exp _ _ _ = exp

renameVars :: Exp -> Dictionary Name -> Exp
renameVars exp rename = renameVar exp rename []

renameVar :: Exp -> Dictionary Name -> [Name] -> Exp
renameVar (LetE decs exp) d notR =
  LetE (replaceDecs decs d notR) (replaceVar exp d VarE (notR ++ getPats decs))
  where
    getPats :: [Dec] -> [Name]
    getPats = concatMap getPats'

    getPats' :: Dec -> [Name]
    getPats' (FunD n _) = [n]
    getPats' (ValD p _ _) = getNamesFromPat p
renameVar exp d notR = replaceVar exp d VarE notR

getName :: Name -> String
getName (Name (OccName n) _) = n

getNamesFromPats :: [Pat] -> [Name]
getNamesFromPats = foldl (\names pat -> names ++ getNamesFromPat pat) []

getNamesFromPat :: Pat -> [Name]
getNamesFromPat (LitP _) = []
getNamesFromPat (VarP n) = [n]
getNamesFromPat (TupP ps) = getNamesFromPats ps
getNamesFromPat (UnboxedTupP _) = []
getNamesFromPat (UnboxedSumP _ _ _) = []
getNamesFromPat (ConP _ _ ps) = getNamesFromPats ps
getNamesFromPat (InfixP _ _ _) = []
getNamesFromPat (UInfixP _ _ _) = []
getNamesFromPat (ParensP p) = getNamesFromPat p
getNamesFromPat (TildeP _) = []
getNamesFromPat (BangP _) = []
getNamesFromPat (AsP n p) = n : getNamesFromPat p
getNamesFromPat WildP = []
getNamesFromPat (RecP _ _) = []
getNamesFromPat (ListP ps) = getNamesFromPats ps
getNamesFromPat (SigP _ _) = []
getNamesFromPat (ViewP _ _) = []

