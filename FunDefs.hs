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
  take 0 _  = []
  take _ [] = []
  take n (x : xs) = if n < 0 then [] else x : take (n - 1) xs

  drop :: Int -> [a] -> [a]
  drop _ [] = []
  drop n (x : xs) = if n <= 0 then (x : xs) else drop (n - 1) xs

  map :: (a -> b) -> [a] -> [b]
  map _ []       = []
  map f (x : xs) = f x : map f xs

  filter :: (a -> Bool) -> [a] -> [a]
  filter _ []       = []
  filter p (x : xs) = if p x
    then x : filter p xs
    else filter p xs

  head :: [a] -> a
  head (x : _) = x

  tail :: [a] -> [a]
  tail (_ : xs) = xs

  last :: [a] -> a
  last [x] = x
  last (x : xs) = last xs

  init :: [a] -> [a]
  init [x] = []
  init (x : xs) = x : init xs

  null :: [a] -> Bool
  null [] = True
  null _ = False

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

  zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
  zipWith f (x : xs) (y : ys) = f x y : zipWith f xs ys
  zipWith _ _        _        = []

  infixr 3 &&
  (&&) :: Bool -> Bool -> Bool
  (&&) False _ = False
  (&&) _     x = x

  infixr 2 ||
  (||) :: Bool -> Bool -> Bool
  (||) True _ = True
  (||) _    x = x

  not :: Bool -> Bool
  not True  = False
  not False = True

  takeWhile :: (a -> Bool) -> [a] -> [a]
  takeWhile _ [] = []
  takeWhile p (x : xs) = if p x
    then x : takeWhile p xs
    else []

  dropWhile :: (a -> Bool) -> [a] -> [a]
  dropWhile _ [] = []
  dropWhile p xs@(x : xs') = if p x
    then dropWhile p xs'
    else xs

  elem :: Eq a => a -> [a] -> Bool
  elem _ [] = False
  elem x (y : ys) = x == y || elem x ys

  notElem :: Eq a => a -> [a] -> Bool
  notElem _ [] = True
  notElem x (y : ys) = x /= y && notElem x ys

  enumFrom :: Enum a => a -> [a]
  enumFrom n = n : enumFrom (succ n)

  enumFromThen :: Enum a => a -> a -> [a]
  enumFromThen n n' = n : n' : worker (f step) (f step n')
    where
      worker s v = v : worker s (s v)
      step = fromEnum n' - fromEnum n
      f 0 y = y
      f n y = if n > 0
        then f (n - 1) (succ y)
        else f (n + 1) (pred y)

  enumFromTo :: (Ord a, Enum a) => a -> a -> [a]
  enumFromTo n m = if n <= m 
    then n : enumFromTo (succ n) m 
    else []

  enumFromThenTo :: (Ord a, Enum a) => a -> a -> a -> [a]
  enumFromThenTo n n' m = worker (f step) n m
    where
      step = fromEnum n' - fromEnum n
      f 0 y = y
      f n y = if n > 0
        then f (n - 1) (succ y)
        else f (n + 1) (pred y)
      worker s v m = if v <= m
        then v : worker s (s v) m 
        else []

  |]

