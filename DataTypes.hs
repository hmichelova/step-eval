module DataTypes where

import Control.Monad
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import qualified Control.Monad.Trans.State as S

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

type Env = (Dictionary, [Dec])

type StateExp = S.StateT Env IO (EitherNone Exp)

type Dictionary = [(Name, Exp)]

type Rename = [(Name, Name)]

data PatternMatch = PMatch Rename
                  | PNomatch
                  | PStep Exp
                  | PException String
                    deriving (Eq, Show)

emptyEnv :: Env
emptyEnv = ([], [])

setDec :: [Dec] -> Env -> Env
setDec d (m, _) = (m, d)

insertVar :: Name -> Exp -> Env -> Env
insertVar n exp (m, d) = ((n, exp) : m, d)

insertDec :: [Dec] -> Env -> Env
insertDec decs (m, d) = (m, decs ++ d)

getVar :: Name -> Env -> Maybe Exp
getVar n (m, _) = lookup n m

getDecs :: Name -> Bool -> Env -> [Dec]
getDecs (Name (OccName n) _) sign (_, d) = filter theSameName d
  where
    theSameName :: Dec -> Bool
    theSameName (SigD (Name (OccName name) _) _) = sign && n == name
    theSameName (FunD (Name (OccName name) _) _) = n == name
    theSameName _             = False

getVars :: Env -> Dictionary
getVars = fst

pprintDictionary :: Dictionary -> String
pprintDictionary d = pprintList $ d
  where
    pprintList :: [(Name, Exp)] -> String
    pprintList [] = ""
    pprintList ((n, e) : xs) = pprint n ++ " -> " ++ pprint e ++ "\n" ++ pprintList xs
