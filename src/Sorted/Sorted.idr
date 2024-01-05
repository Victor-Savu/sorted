module Sorted.Sorted

import Control.Order
import Control.Relation
import Data.Void

import Sorted.Occurs
import Sorted.Relates

%default total

public export
data Sorted: LinearOrder a rel => List a -> Type where
    NilIsSorted: (0 lo: LinearOrder a rel) => Sorted @{lo} Nil
    SingletonIsSorted : (0 lo: LinearOrder a rel) => Sorted @{lo} [x]
    SeveralAreSorted: {x, y: a} -> rel x y -> (0 lo: LinearOrder a rel) => Sorted @{lo} (y::ys) -> Sorted @{lo} (x::y::ys)

public export
tail : (0 lo: LinearOrder a rel) => Sorted @{lo} (x::xs) -> Sorted @{lo} xs
tail SingletonIsSorted = NilIsSorted
tail (SeveralAreSorted z w) = w

public export
head : (lo: LinearOrder a rel) => Sorted @{lo} (x::xs) -> RelatesToAll rel x xs
head SingletonIsSorted z = absurdity @{uninhabitedOccursAtLeastOnceInNil} z
head (SeveralAreSorted y _) (Here _) = y
head (SeveralAreSorted y w) (There z f) = transitive y $ head w z
