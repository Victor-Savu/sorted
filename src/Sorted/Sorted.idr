module Sorted.Sorted

import Control.Order
import Control.Relation
import Data.Void

import Sorted.Occurs
import Sorted.Relates

%default total

infixr 4 :@:

||| A list sorted according to a relation over the type of its elements.
public export
data Sorted: Rel a -> List a -> Type where
    ||| An empty list is always sorted.
    Nil: Sorted rel []

    ||| A list with a single element is always sorted.
    Singleton : Sorted rel [x]

    ||| Rel must induce a linear order over the type of elements in order to be useful for sorting.
    ||| If an element x relates to the head y of a sorted list y::ys, then x::y::ys is also sorted with respect to rel.
    (:@:): LinearOrder a rel => {x, y: a} -> rel x y -> Sorted rel (y::ys) -> Sorted rel (x::y::ys)

infixr 4 -=@

||| An alternative notation for a sorted list
public export
(-=@) : List a -> Rel a -> Type
(-=@) xs rel = Sorted rel xs

||| The tail of a sorted list is also a sorted list.
public export
tail : LinearOrder a rel => (x::xs) -=@ rel -> xs -=@ rel
tail Singleton = Nil
tail (_ :@: w) = w

||| The head of a sorted list is relates to all of the elements in the tail of the list.
public export
head : (x::xs) -=@ rel -> RelatesToAll rel x xs
head Singleton z = absurdity @{uninhabitedOccursAtLeastOnceInNil} z
head (y :@: _) (Here _) = y
head (y :@: w) (There z _) = transitive y $ head w z
