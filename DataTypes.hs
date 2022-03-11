module DataTypes where

import Control.Monad
import Language.Haskell.TH
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

type Env a = M.Map Name a

