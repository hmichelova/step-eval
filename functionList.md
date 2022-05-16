## Functions with available declarations

```haskell
id :: a -> a
const :: a -> b -> a
take :: Int -> [a] -> [a]
drop :: Int -> [a] -> [a]
map :: (a -> b) -> [a] -> [b]
filter :: (a -> Bool) -> [a] -> [a]
head :: [a] -> a
tail :: [a] -> [a]
last :: [a] -> a
init :: [a] -> [a]
null :: [a] -> Bool
length :: [a] -> Int
fst :: (a, b) -> a
snd :: (a, b) -> b
zip :: [a] -> [b] -> [(a, b)]
zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
(&&) :: Bool -> Bool -> Bool
(||) :: Bool -> Bool -> Bool
not :: Bool -> Bool
takeWhile :: (a -> Bool) -> [a] -> [a]
dropWhile :: (a -> Bool) -> [a] -> [a]
elem :: Eq a => a -> [a] -> Bool
notElem :: Eq a => a -> [a] -> Bool
enumFrom :: Enum a => a -> [a]
enumFromThen :: Enum a => a -> a -> [a]
enumFromTo :: (Ord a, Enum a) => a -> a -> [a]
enumFromThenTo :: (Ord a, Enum a) => a -> a -> a -> [a]
```
