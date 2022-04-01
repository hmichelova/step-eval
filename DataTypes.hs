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

type Env = (Dictionary Exp, [Dec])

type StateExp = S.StateT Env IO (EitherNone Exp)

type Dictionary a = [(Name, a)]

data PatternMatch = PMatch (Dictionary Name)
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

updateOrInsertVar :: Name -> Exp -> Env -> Env
updateOrInsertVar n exp (m, d) = case lookup n m of
  Nothing -> ((n, exp) : m, d)
  Just v -> (map (\(n', e') -> if n' == n then (n, exp) else (n', e')) m, d)

insertDec :: [Dec] -> Env -> Env
insertDec decs (m, d) = (m, decs ++ d)

getVar :: Name -> Env -> Maybe Exp
getVar n (m, _) = lookup n m

getVars :: Env -> Dictionary Exp
getVars = fst

pprintDictionary :: Ppr a => Dictionary a -> String
pprintDictionary [] = ""
pprintDictionary ((n, e) : xs) = pprint n ++ " -> " ++ pprint e ++ "\n" ++ pprintDictionary xs

