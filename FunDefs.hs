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

  last :: [a] -> a
  last [x] = x
  last (x : xs) = last xs

  length :: [a] -> Int
  length [] = 0
  length (_ : xs) = 1 + length xs

  fst :: (a, b) -> a
  fst (x, _) = x

  snd :: (a, b) -> b
  snd (_, x) = x

  zip :: [a] -> [b] -> [(a, b)]
  zip [] _ = []
  zip _ [] = []
  zip (x : xs) (y : ys) = (x, y) : zip xs ys

  zipWith' :: (a -> b -> c) -> [a] -> [b] -> [c]
  zipWith' f = go
    where
      go [] _ = []
      go _ [] = []
      go (x : xs) (y : ys) = f x y : go xs ys

  zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
  zipWith f (x : xs) (y : ys) = f x y : zipWith f xs ys
  zipWith _ _        _        = []

  |]

