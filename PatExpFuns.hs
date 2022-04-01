module PatExpFuns where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

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

replaceDecs :: [Dec] -> Dictionary Name -> [Dec]
replaceDecs decs rename = map replaceDec decs
  where
    replaceDec :: Dec -> Dec
    replaceDec (FunD name clauses) = FunD name $ map replaceClauses clauses
    replaceDec dec = dec

    replaceClauses :: Clause -> Clause
    replaceClauses (Clause pats body decs) =
      let rename' = filter (\(_, n) -> all (notInPats n) pats) rename in
        Clause pats (replaceBody body rename') (replaceDecs decs rename')
      where
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

    replaceBody :: Body -> Dictionary Name -> Body
    replaceBody (NormalB exp) rename = NormalB $ replaceVars exp rename VarE
    replaceBody b _ = b -- TODO guards

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
replaceVar le@(LamE pats exp) n e f = if elem n (getNamesFromPats pats)
  then le
  else LamE pats $ replaceVar exp n e f
replaceVar (TupE mexps) n e f =
  TupE $ map (maybe Nothing (\e' -> Just (replaceVar e' n e f))) mexps
replaceVar (CondE b t f) n e fun =
  CondE (replaceVar b n e fun) (replaceVar t n e fun) (replaceVar f n e fun)
-- TODO let
replaceVar (ListE xs) n e f = ListE $ map (\exp -> replaceVar exp n e f) xs
replaceVar (ArithSeqE range) n e f = ArithSeqE $ replaceVarRange range
  where
    replaceVarRange :: Range -> Range
    replaceVarRange (FromR fr) = FromR $ replaceVar fr n e f
    replaceVarRange (FromThenR fr th) = FromThenR (replaceVar fr n e f) $ replaceVar th n e f
    replaceVarRange (FromToR fr to) = FromToR (replaceVar fr n e f) $ replaceVar to n e f
    replaceVarRange (FromThenToR fr th to) = FromThenToR (replaceVar fr n e f)
                                                         (replaceVar th n e f)
                                                         (replaceVar to n e f)
    
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

