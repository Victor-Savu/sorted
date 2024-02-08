module Sorted.Sorted

import Control.Function
import Control.Order
import Control.Relation
import Data.Nat
import Data.Void
import Decidable.Equality

import Sorted.Container
import Sorted.Relates

%default total

infixr 4 :@:

%hide Stream.(::)
%hide Prelude.(::)
%hide Relates.(::)
%hide Relates.Nil
%hide Prelude.Nil

||| A list sorted according to a relation over the type of its elements.
public export
data Sorted: (lo: LinearOrder a rel) => (ct: Container a c) => c -> Type where
    ||| An empty list is always sorted.
    Nil:  Sorted @{lo} @{ct} ([] @{ct})

    ||| A list with a single element is always sorted.
    Singleton : (x: a) -> Sorted @{lo} @{ct} {rel} ((x :: ([] @{ct}))  @{ct})

    ||| Rel must induce a linear order over the type of elements in order to be useful for sorting.
    ||| If an element x relates to the head y of a sorted list y::ys, then x::y::ys is also sorted with respect to rel.
    (:@:): {x, y: a} -> {ys: c} -> rel x y -> Sorted @{lo} @{ct} {c} {a} {rel} ((y :: ys) @{ct}) -> Sorted {rel} @{lo} @{ct} {c} {a} ((x :: (y::ys) @{ct}) @{ct})

||| If x relates to all the elements of xs and xs is sorted with respect to the linear order induced by rel,
||| then x::xs is also sorted with respect to the same linear order.
export
0 (::) : DecEq a => LinearOrder a rel => Container a c => RelatesToAll {c} rel x xs -> Sorted {c} {rel} xs -> Sorted {c} {rel} ((x::xs) {c})
(::) f [] = Singleton x
(::) f (Singleton {x=x'}) = (f $ sym ConsAddsOne \=> cong S NilIsEmpty) :@: Singleton x'
(::) f ((relX'Y :@: sortedYYs) {x=x'} {ys} {y}) = (f $ sym ConsAddsOne) :@: relX'Y :@: sortedYYs

infixr 4 -=@

||| An alternative notation for a sorted list
export
(-=@) : LinearOrder a rel => Container a c => c -> Type
(-=@) xs = Sorted {rel} xs

||| The tail of a sorted list is also a sorted list.
export
0 tail : LinearOrder a rel => Container a c => {x: a} -> {ysIsCons: x::xs = ys} -> (Sorted {rel} {c} ys) -> (Sorted {c} {rel} xs)
tail [] = absurdity @{uninhabitedConsIsNil} ysIsCons
tail (Singleton y) = replace {p = \q => Sorted {rel} {c} q} (sym $ snd $ biinjective @{ConsBiinjective {c}} ysIsCons) []
tail (relXY :@: sortedYYs) = replace {p = \q => Sorted {rel} {c} q} (sym $ snd $ biinjective @{ConsBiinjective {c}} ysIsCons) sortedYYs

||| The head of a sorted list is relates to all of the elements in the tail of the list.
export
0 head : LinearOrder a rel => Container a c => DecEq a => {ysIsCons: x::xs = ys} -> Sorted {c} {rel} ys -> RelatesToAll {c} rel x xs
head [] _ = absurdity @{uninhabitedConsIsNil} ysIsCons
head (Singleton y) prf = void $ SIsNotZ $ (sym prf) \=> ((cong (guest .#.) $ snd $ biinjective @{ConsBiinjective {c}} ysIsCons) \=> NilIsEmpty)
head ((relXY :@: sortedYYs) {x=x'} {y} {ys}) prf with (biinjective @{ConsBiinjective {c}} ysIsCons)
  head ((relXY :@: sortedYYs) {x=x'} {y = y} {ys = ys}) prf | (Refl, Refl) with (decEq guest y)
    head ((relXY :@: sortedYYs) {x=x'} {y = y} {ys = ys}) prf | (Refl, Refl) | (Yes Refl) = relXY
    head ((relXY :@: sortedYYs) {x=x'} {y = y} {ys = ys}) prf | (Refl, Refl) | (No guestNEqY) = relXY \=> (head {x=y} {xs=ys} {ys=y::ys} {ysIsCons=Refl} sortedYYs (ConsKeepsRest guestNEqY \=> prf))
