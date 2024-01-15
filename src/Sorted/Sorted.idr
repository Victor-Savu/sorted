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
data Sorted: (lo: LinearOrder a rel) => (ct: Container a c) => c a -> Type where
    ||| An empty list is always sorted.
    Nil:  Sorted @{lo} @{ct} ([] @{ct})

    ||| A list with a single element is always sorted.
    Singleton : (x: a) -> Sorted @{lo} @{ct} {rel} ((x :: ([] @{ct}))  @{ct})

    ||| Rel must induce a linear order over the type of elements in order to be useful for sorting.
    ||| If an element x relates to the head y of a sorted list y::ys, then x::y::ys is also sorted with respect to rel.
    (:@:): {x, y: a} -> {ys: c a} -> rel x y -> Sorted @{lo} @{ct} {c} {a} {rel} ((y :: ys) @{ct}) -> Sorted {rel} @{lo} @{ct} {c} {a} ((x :: (y::ys) @{ct}) @{ct})

||| If x relates to all the elements of xs and xs is sorted with respect to the linear order induced by rel,
||| then x::xs is also sorted with respect to the same linear order.
public export
0 (::) : DecEq a => (lo: LinearOrder a rel) => RelatesToAll @{ct} rel x xs -> Sorted @{lo} @{ct} xs -> Sorted @{lo} @{ct} ((x::xs) @{ct})
(::) f [] = Singleton x
(::) f (Singleton {x=x'}) = (f $ sym (ConsAddsOne x' Container.Nil) `transitive` (cong S $ NilIsEmpty x')) :@: Singleton x'
(::) f ((relX'Y :@: sortedYYs) {x=x'} {ys} {y}) = (f $ sym $ ConsAddsOne @{ct} x' (y::ys)) :@: relX'Y :@: sortedYYs

infixr 4 -=@

||| An alternative notation for a sorted list
public export
(-=@) : LinearOrder a rel => Container a c => c a -> Type
(-=@) xs = Sorted {rel} xs

||| The tail of a sorted list is also a sorted list.
public export
0 tail : {x': a} -> {xs', ys': c a} -> (lo: LinearOrder a rel) => (ct: Container a c) => {ysIsCons: x'::xs' = ys'} ->  (Sorted @{lo} @{ct} {rel} {c} {a} ys') -> (Sorted @{lo} @{ct} {c} {a} {rel} xs')
tail [] = absurdity @{uninhabitedConsIsNil} ysIsCons
tail (Singleton y) = replace {p = \q => Sorted @{lo} @{ct} q} (sym $ snd $ biinjective @{ConsBiinjective @{ct} {c} {a} y} ysIsCons) []
tail (relXY :@: sortedYYs) = replace {p = \q => Sorted @{lo} @{ct} q} (sym $ snd $ biinjective @{ConsBiinjective @{ct} {c} {a}  x'} ysIsCons) sortedYYs

||| The head of a sorted list is relates to all of the elements in the tail of the list.
covering
public export
0 head : {rel: a->a->Type} -> {x: a} -> {xs, ys: c a} -> (lo: LinearOrder a rel) => (ct: Container a c) => DecEq a => {ysIsCons: x::xs = ys} -> Sorted @{lo} ys -> RelatesToAll @{ct} rel x xs
head [] _ = absurdity @{uninhabitedConsIsNil} ysIsCons
head (Singleton y) prf = void $ SIsNotZ $ (sym prf) `transitive` ((cong (guest .#.) $ snd $ biinjective @{ConsBiinjective @{ct} {c} {a} x} ysIsCons) `transitive` (NilIsEmpty guest))
head ((relXY :@: sortedYYs) {x=x'} {y} {ys}) prf with (biinjective @{ConsBiinjective @{ct} {c} {a} x} ysIsCons)
  head ((relXY :@: sortedYYs) {x=x'} {y = y} {ys = ys}) prf | (Refl, Refl) with (decEq guest y)
    head ((relXY :@: sortedYYs) {x=x'} {y = y} {ys = ys}) prf | (Refl, Refl) | (Yes Refl) = relXY
    head ((relXY :@: sortedYYs) {x=x'} {y = y} {ys = ys}) prf | (Refl, Refl) | (No guestNEqY) = relXY `transitive` (head {x=y} {xs=ys} {ys=y::ys} {ysIsCons=Refl} sortedYYs (ConsKeepsRest y ys guest guestNEqY `transitive` prf))
