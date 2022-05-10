module DataTypes where

import Control.Monad
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import qualified Control.Monad.Trans.State as S
import qualified Data.Map as M

data StepExp a = Exception String
               | None
               | Value a
                 deriving (Eq, Show)

instance Functor StepExp where
  fmap _ (Exception e) = Exception e
  fmap _ None          = None
  fmap f (Value a)     = Value $ f a

instance Applicative StepExp where
  pure = Value
  Exception e <*> _ = Exception e
  None        <*> _ = None
  Value f     <*> r = fmap f r

instance Monad StepExp where
  Exception e >>= _ = Exception e
  None        >>= _ = None
  Value v     >>= f = f v

type IOStepExp a = IO (StepExp a)

type StateExp = S.StateT Env IO (StepExp Exp)

data Env = Env (Dictionary Exp) [Dec] [Dec]

type Dictionary a = M.Map Name a

data PatternMatch = PMatch (Dictionary Name)
                  | PNomatch
                  | PStep Exp
                  | PException String
                    deriving (Eq, Show)

emptyEnv :: Env
emptyEnv = Env M.empty [] []

setDefaultDec :: [Dec] -> Env -> Env
setDefaultDec d (Env m c _) = Env m c d

insertVar :: Name -> Exp -> Env -> Env
insertVar n exp (Env m c d) = Env (M.insert n exp m) c d

updateOrInsertVar :: Name -> Exp -> Env -> Env
updateOrInsertVar n exp (Env m c d) = Env (M.insertWith const n exp m) c d

insertDec :: [Dec] -> Env -> Env
insertDec decs (Env m c d) = Env m (decs ++ c) d

getVar :: Name -> Env -> Maybe Exp
getVar n (Env m _ _) = M.lookup n m

getVars :: Env -> Dictionary Exp
getVars (Env m _ _) = m

