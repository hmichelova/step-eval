{-# LANGUAGE TemplateHaskell #-}

module FunDefs (funcs) where

import Language.Haskell.TH

funcs :: Q [Dec]
funcs = [d|
  id :: a -> a
  id x = x

  const :: a -> b -> a
  const x _ = x

  take :: Int -> [a] -> [a]
  take _ [] = []
  take 0 _  = []
  take n (x : xs) = if n < 0 then [] else x : take (n - 1) xs

  map :: (a -> b) -> [a] -> [b]
  map _ []       = []
  map f (x : xs) = f x : map f xs

  filter :: (a -> Bool) -> [a] -> [a]
  filter _ []       = []
  filter p (x : xs) = if p x
    then x : filter p xs
    else filter p xs

  |]

