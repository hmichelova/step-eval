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

data Env = Env (Dictionary Exp) [Dec] [Dec] Change

type Change = (ChangeT, String)
data ChangeT = NoChange
             | Change -- TODO update

type Dictionary a = M.Map Name a

data PatternMatch = PMatch (Dictionary Name)
                  | PNomatch
                  | PStep Exp
                  | PException String
                    deriving (Eq, Show)

emptyEnv :: Env
emptyEnv = Env M.empty [] [] emptyChange

setDefaultDec :: [Dec] -> Env -> Env
setDefaultDec d (Env m c _ ch) = Env m c d ch

insertVar :: Name -> Exp -> Env -> Env
insertVar n exp (Env m c d ch) = Env (M.insert n exp m) c d ch

updateOrInsertVar :: Name -> Exp -> Env -> Env
updateOrInsertVar n exp (Env m c d ch) = Env (M.insertWith const n exp m) c d ch

insertDec :: [Dec] -> Env -> Env
insertDec decs (Env m c d ch) = Env m (decs ++ c) d ch

emptyChange :: Change
emptyChange = (NoChange, "")

removeChange :: Env -> Env
removeChange (Env m c d _) = Env m c d emptyChange

insertChange :: Env -> ChangeT -> String -> Env
insertChange (Env m c d _) ct s = Env m c d (ct, s)

getChange :: Env -> Change
getChange (Env _ _ _ ch) = ch

getChangeString :: Env -> String
getChangeString (Env _ _ _ (_, s)) = s

printChange :: Env -> String
printChange (Env _ _ _ (NoChange, _)) = "-- No sub-expression changed."
printChange (Env _ _ _ (Change, s)) = "-- Evaluated sub-expression is in { }: " ++ s

getVar :: Name -> Env -> Maybe Exp
getVar n (Env m _ _ _) = M.lookup n m

getVars :: Env -> Dictionary Exp
getVars (Env m _ _ _) = m

fromValue :: StepExp a -> a
fromValue (Value v) = v
