module DataTypes where

import Control.Monad
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import qualified Control.Monad.Trans.State as S
import qualified Data.Map as M

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

type Env = (Dictionary Exp, [Dec], [Dec])

type StateExp = S.StateT Env IO (EitherNone Exp)

type Dictionary a = M.Map Name a

data PatternMatch = PMatch (Dictionary Name)
                  | PNomatch
                  | PStep Exp
                  | PException String
                    deriving (Eq, Show)

emptyEnv :: Env
emptyEnv = (M.empty, [], [])

setDefaultDec :: [Dec] -> Env -> Env
setDefaultDec d (m, c, _) = (m, c, d)

insertVar :: Name -> Exp -> Env -> Env
insertVar n exp (m, c, d) = (M.insert n exp m, c, d)

updateOrInsertVar :: Name -> Exp -> Env -> Env
updateOrInsertVar n exp (m, c, d) = (M.insertWith const n exp m, c, d)

insertDec :: [Dec] -> Env -> Env
insertDec decs (m, c, d) = (m, decs ++ c, d)

getVar :: Name -> Env -> Maybe Exp
getVar n (m, _, _) = M.lookup n m

getVars :: Env -> Dictionary Exp
getVars (m, _, _) = m

pprintDictionary :: Ppr a => Dictionary a -> String
pprintDictionary [] = ""
pprintDictionary ((n, e) : xs) = pprint n ++ " -> " ++ pprint e ++ "\n" ++ pprintDictionary xs

