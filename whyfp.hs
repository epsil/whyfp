-- Exclude Haskell primitives defined in the article

import Prelude hiding (foldr, sum, product, length, (.), map, iterate,
                       sqrt, zipWith, maximum, minimum, take)
import Data.List (intersperse)
import qualified Data.List as D (sort, sortBy)
import qualified Prelude as P (map, foldr, sum, length, maximum,
                               minimum, take)

-- Gluing Functions Together

data List a = Cons a (List a) | Nil deriving Show

sum = foldr (+) 0

foldr f x Nil = x
foldr f x (Cons a l) = f a (foldr f x l)

product = foldr (*) 1

or = foldr (||) False

and = foldr (&&) True

append a b = foldr Cons b a

length = foldr count 0
count a n = n + 1

double n = 2 * n

(f . g) h = f (g h)

doubleAll = map double
map f = foldr (Cons . f) Nil

sumMatrix = sum . map sum

data Tree a = Node a (List (Tree a)) deriving Show

foldTree f g a (Node label subtrees) =
    f label (foldr (g . foldTree f g a) a subtrees)

sumTree = foldTree (+) (+) 0

labels = foldTree Cons append Nil

mapTree f = foldTree (Node . f) Cons Nil

-- Gluing Programs Together

--- Newton-Raphson Square Roots

next n x = (x + n / x) / 2

iterate f a = Cons a (iterate f (f a))

within eps (Cons a (Cons b rest))
    | abs (a - b) <= eps = b
    | otherwise          = within eps (Cons b rest)

sqrt a0 eps n = within eps (iterate (next n) a0)

relative eps (Cons a (Cons b rest))
    | abs (a / b - 1) <= eps = b
    | otherwise              = relative eps (Cons b rest)

relativeSqrt a0 eps n = relative eps (iterate (next n) a0)

--- Numerical Differentiation

easyDiff f x h = (f (x + h) - f x) / h

differentiate h0 f x = map (easyDiff f x) (iterate halve h0)
halve x = x / 2

elimError n (Cons a (Cons b rest)) =
    Cons ((b * (2 ** n) - a) / (2 ** n - 1))
         (elimError n (Cons b rest))

order (Cons a (Cons b (Cons c rest))) =
    fromIntegral (round (logBase 2 ((a - c) / (b - c) - 1)))

improve s = elimError (order s) s

super s = map second (iterate improve s)
second (Cons a (Cons b rest)) = b

--- Numerical Integration

easyIntegrate f a b = (f a + f b) * (b - a) / 2

zipWith f (Cons a s) (Cons b t) = Cons (f a b) (zipWith f s t)

integrate f a b = integ f a b (f a) (f b)
integ f a b fa fb =
    Cons ((fa + fb) * (b - a) / 2)
         (zipWith (+) (integ f a m fa fm)
                      (integ f m b fm fb))
    where m  = (a + b) / 2
          fm = f m

-- An Example from Artificial Intelligence

repTree f a = Node a (map (repTree f) (f a))

gameTree p = repTree moves p

maximize (Node n Nil)  =  Cons n Nil
maximize (Node n l)    =  mapMin (map minimize l)

minimize (Node n Nil)  =  Cons n Nil
minimize (Node n l)    =  mapMax (map maximize l)

mapMin  (Cons nums rest) =
        Cons (minimum nums) (omit (minimum nums) rest)

mapMax  (Cons nums rest) =
        Cons (maximum nums) (omit (maximum nums) rest)

omit pot Nil = Nil
omit pot (Cons nums rest)
    | minLeq nums pot  =  omit pot rest
    | otherwise        =  Cons  (minimum nums)
                                (omit (minimum nums) rest)
minLeq Nil pot = False
minLeq (Cons n rest) pot
    | n <= pot   =  True
    | otherwise  =  minLeq rest pot

highFirst (Node n sub) = Node n (sortBy higher (map lowFirst sub))
lowFirst (Node n sub) = Node n (sortBy (flip higher) (map highFirst sub))
higher (Node n1 sub1) (Node n2 sub2) = compare n2 n1

evaluate =
    maximum . maximize . highFirst . mapTree static . prune 8 . gameTree

takeTree n = foldTree (nodett n) Cons Nil
nodett n label sub = Node label (take n sub)

prune 0 (Node pos sub)
    | dynamic pos  =  Node pos (map (prune 0) sub)
    | otherwise    =  Node pos Nil
prune n (Node a x)  =  Node a (map (prune (n - 1)) x)

data Square = Empty | Nought | Cross
    deriving Eq

instance Show Square where
  show Empty  = " "
  show Nought = "O"
  show Cross  = "X"

data Board = Board [[Square]]
  deriving Eq

instance Show Board where
  show (Board rows) =
    "\n" ++ concat (intersperse "-+-+-\n" $ map' showRow rows) ++ "\n"
    where showRow cols = concat (intersperse "|" $ map' show cols) ++ "\n"

type Position = Board

emptyBoard = Board [[Empty,Empty,Empty],
                    [Empty,Empty,Empty],
                    [Empty,Empty,Empty]]

update i x [] = []
update i x (y:ys)
  | i == 0 = x : ys
  | otherwise = y : update (i - 1) x ys

move :: Int -> Int -> Square -> Board -> Board
move x y p (Board b) = Board (update y (update x p (b !! y)) b)

getSquare :: Int -> Int -> Board -> Square
getSquare x y (Board b) = (b !! y) !! x

moves :: Board -> List Board
moves b = toList [move x y p b | y <- [0..2],
                                 x <- [0..2],
                                 getSquare x y b == Empty]
          where p = if countPlayer Cross b <= countPlayer Nought b
                    then Cross
                    else Nought
                countPlayer p (Board b) =
                    sum' $ map' (length' . filter (==p)) b

static = static' Cross

static' :: Square -> Board -> Integer
static' user (Board b) =
      case b of
           [[a, _, _],
            [_, b, _],
            [_, _, c]] | eq a b c -> win a user

           [[_, _, a],
            [_, b, _],
            [c, _, _]] | eq a b c -> win a user

           [[a, b, c],
            [_, _, _],
            [_, _, _]] | eq a b c -> win a user

           [[_, _, _],
            [a, b, c],
            [_, _, _]] | eq a b c -> win a user

           [[_, _, _],
            [_, _, _],
            [a, b, c]] | eq a b c -> win a user

           [[a, _, _],
            [b, _, _],
            [c, _, _]] | eq a b c -> win a user

           [[_, a, _],
            [_, b, _],
            [_, c, _]] | eq a b c -> win a user

           [[_, _, a],
            [_, _, b],
            [_, _, c]] | eq a b c -> win a user

           _ -> 0
    where
        eq a b c = a == b && b == c && a /= Empty
        win a user = if a == user then 1 else -1

dynamic p = False

sort' :: (Ord a) => [a] -> [a]
sort' = D.sort

sortBy' = D.sortBy

sort :: Ord a => List a -> List a
sort = toList . sort' . fromList

sortBy :: (a -> a -> Ordering) -> List a -> List a
sortBy compare = toList . sortBy' compare . fromList

take' :: Int -> [a] -> [a]
take' = P.take

take :: Int -> List a -> List a
take n = toList . take' n . fromList

map' = P.map
foldr' = P.map
sum' = P.sum
length' = P.length

maximum' :: (Ord a) => [a] -> a
maximum' = P.maximum
minimum' :: (Ord a) => [a] -> a
minimum' = P.minimum

maximum :: (Ord a) => List a -> a
maximum l = maximum' (fromList l)

minimum :: (Ord a) => List a -> a
minimum l = minimum' (fromList l)

toList :: [a] -> List a
toList [] = Nil
toList (x:xs) = Cons x (toList xs)

fromList :: List a -> [a]
fromList Nil = []
fromList (Cons x xs) = x : fromList xs
