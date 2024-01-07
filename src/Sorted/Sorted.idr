module Sorted.Sorted

import Control.Order
import Control.Relation
import Data.Void
import Decidable.Equality

import Sorted.Occurs
import Sorted.Relates

%default total

infixr 4 :@:

||| A list sorted according to a relation over the type of its elements.
public export
data Sorted: (0 lo: LinearOrder a rel) -> List a -> Type where
    ||| An empty list is always sorted.
    Nil:  Sorted lo []

    ||| A list with a single element is always sorted.
    Singleton : Sorted lo [x]

    ||| Rel must induce a linear order over the type of elements in order to be useful for sorting.
    ||| If an element x relates to the head y of a sorted list y::ys, then x::y::ys is also sorted with respect to rel.
    (:@:): {x, y: a} -> rel x y -> Sorted lo (y::ys) -> Sorted {rel} lo (x::y::ys)

||| If x relates to all the elements of xs and xs is sorted with respect to the linear order induced by rel,
||| then x::xs is also sorted with respect to the same linear order.
public export
0 (::) : DecEq a => (lo: LinearOrder a rel) => RelatesToAll rel x xs -> Sorted lo xs -> Sorted lo (x::xs)
(::) f [] = Singleton
(::) f Singleton = (f $ Here Nowhere) :@: Singleton
(::) f ((y :@: z)) = head {rel} f :@: y :@: z

infixr 4 -=@

||| An alternative notation for a sorted list
public export
(-=@) : List a -> LinearOrder a rel -> Type
(-=@) xs lo = Sorted lo xs

||| The tail of a sorted list is also a sorted list.
public export
tail : (x::xs) -=@ rel -> xs -=@ rel
tail Singleton = Nil
tail (_ :@: w) = w

||| The head of a sorted list is relates to all of the elements in the tail of the list.
public export
head : (lo: LinearOrder a rel) => (x::xs) -=@ lo -> RelatesToAll rel x xs
head Singleton z = absurdity @{uninhabitedOccursAtLeastOnceInNil} z
head (y :@: _) (Here _) = y
head (y :@: w) (There z _) = transitive y $ head w z
