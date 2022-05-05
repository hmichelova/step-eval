module PatExpFuns where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import qualified Data.Map as M

import DataTypes

getDecs :: Name -> Bool -> Env -> [Dec]
getDecs (Name (OccName n) _) sign (_, d) = filter theSameName d
  where
    theSameName :: Dec -> Bool
    theSameName (SigD (Name (OccName name) _) _) = sign && n == name
    theSameName (FunD (Name (OccName name) _) _) = n == name
    theSameName (ValD pat _ _) = any (\(Name (OccName name) _) -> n == name) $ getNamesFromPat pat
    theSameName _             = False

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
replaceDecs decs rename notR = map (flip replaceDec notR) decs
  where
    replaceDec :: Dec -> [Name] -> Dec
    replaceDec (FunD name clauses) notR = FunD name $ map (flip replaceClauses notR) clauses
    replaceDec (ValD pat body whereDec) notR =
      ValD pat (replaceBody body rename (getNamesFromPats [pat] ++ notR))
               (replaceDecs whereDec rename (getNamesFromPats [pat] ++ notR))
    replaceDec dec _ = dec

    replaceClauses :: Clause -> [Name] -> Clause
    replaceClauses (Clause pats body decs) notR =
      Clause pats (replaceBody body rename (getNamesFromPats pats ++ notR))
                  (replaceDecs decs rename (getNamesFromPats pats ++ notR))
      where

    replaceBody :: Body -> Dictionary Name -> [Name] -> Body
    replaceBody (NormalB exp) rename notR = NormalB $ replaceVar exp rename VarE notR
    replaceBody b _ _ = b -- TODO guards

    notInPats :: Name -> Pat -> Bool
    notInPats name (VarP n) = n /= name
    notInPats name (TupP ps) = all (notInPats name) ps
    notInPats name (UnboxedTupP ps) = all (notInPats name) ps
    notInPats name (UnboxedSumP p _ _) = notInPats name p
    notInPats name (ConP n _ ps) = name /= n && all (notInPats name) ps
    notInPats name (InfixP p1 n p2) = name /= n && all (notInPats name) [p1, p2]
    notInPats name (UInfixP p1 n p2) = name /= n && all (notInPats name) [p1, p2]
    notInPats name (ParensP p) = notInPats name p
    notInPats name (TildeP p) = notInPats name p
    notInPats name (BangP p) = notInPats name p
    notInPats name (AsP n p) = name /= n && notInPats name p
    notInPats name (RecP n _) = name /= n
    notInPats name (ListP ps) = all (notInPats name) ps
    notInPats name (SigP p _) = notInPats name p
    notInPats name (ViewP _ p) = notInPats name p
    notInPats _ _ = True

replaceVars :: Exp -> Dictionary a -> (a -> Exp) -> Exp
replaceVars exp rename f = replaceVar exp rename f []

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
-- TODO let
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
    
replaceVar exp _ _ _ = exp -- TODO

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

