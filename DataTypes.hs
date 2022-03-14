module DataTypes where

import Control.Monad
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import qualified Data.Map as M
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

type Env = (M.Map Name Exp, [Dec])

type StateExp = S.StateT Env IO (EitherNone Exp)

emptyEnv :: Env
emptyEnv = (M.empty, [])

setDec :: [Dec] -> Env -> Env
setDec d (m, _) = (m, d)

insertVar :: Name -> Exp -> Env -> Env
insertVar n exp (m, d) = (M.insert n exp m, d)

insertDec :: [Dec] -> Env -> Env
insertDec decs (m, d) = (m, decs ++ d)

getVar :: Name -> Env -> Maybe Exp
getVar n (m, _) = M.lookup n m

getDecs :: Name -> Bool -> Env -> [Dec]
getDecs (Name (OccName n) _) sign (_, d) = filter theSameName d
  where
    theSameName :: Dec -> Bool
    theSameName (SigD (Name (OccName name) _) _) = sign && n == name
    theSameName (FunD (Name (OccName name) _) _) = n == name
    theSameName _             = False

getVarList :: Env -> [(Name, Exp)]
getVarList (m, _) = M.toList m

