module Sorted.Sorted

import Control.Order
import Control.Relation
import Data.Void

import Sorted.Occurs
import Sorted.Relates

%default total

public export
data Sorted: LinearOrder a rel => List a -> Type where
    NilIsSorted: Sorted @{_} []
    SingletonIsSorted : Sorted @{_} [x]
    SeveralAreSorted: {x, y: a} -> rel x y -> Sorted @{lo} {rel=rel} (y::ys) -> Sorted @{lo} {rel=rel} (x::y::ys)

public export
tail : LinearOrder a rel => Sorted {rel=rel} (x::xs) -> Sorted {rel=rel} xs
tail SingletonIsSorted = NilIsSorted
tail (SeveralAreSorted z w) = w

public export
head : LinearOrder a rel => Sorted {rel=rel} (x::xs) -> RelatesToAll rel x xs
head SingletonIsSorted z = absurdity @{uninhabitedOccursAtLeastOnceInNil} z
head (SeveralAreSorted y _) (Here _) = y
head (SeveralAreSorted y w) (There z f) = transitive y $ head w z
