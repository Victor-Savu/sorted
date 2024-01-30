module Sorted.Relates

import Control.Relation
import Data.Nat
import Decidable.Equality

import Sorted.Container
import Sorted.IsPermutationOf

%default total

||| The type of proofs that a value relates to all the elements of a list.
public export
RelatesToAll : {a: Type} -> Container a c => Rel a -> a -> c -> Type
RelatesToAll relates socialButterfly party = {guest: a} -> {n: Nat} -> guest .#. party = (S n) -> relates socialButterfly guest

infixr 4 -@->

||| If x relates to all the elements of xs , then it relates to any permutation ys of the elements of xs
export
(-@->) : {x: a} -> {xs, ys: c} -> Container a c => RelatesToAll rel x xs -> (xs ~@~ ys) -> DecEq a => RelatesToAll rel x ys
(-@->) f (Ipo g) y = f (g guest \=> y)


%hide Prelude.(::)
%hide Prelude.Nil
%hide Stream.(::)

export
0 Nil : {0 x: a} -> Container a c => RelatesToAll {c} rel x Container.Nil
Nil prf with (sym prf \=> (NilIsEmpty {c} guest))
  Nil prf | _ impossible

||| If x relates to y and x also relates to all the elements of the list xs then x relates to all the elements of y::xs
export
0 (::) : {rel: Rel a} -> {xs: c} -> rel x y -> DecEq a => Container a c => RelatesToAll rel x xs -> RelatesToAll rel x (y::xs)
(::) relXY f prf with (decEq guest y)
  (::) relXGuest f prf | (Yes Refl) = relXGuest
  (::) relXY f prf | (No guestNEqY) = f $ ConsKeepsRest y xs guest guestNEqY \=> prf

||| If e relates to all the elements in a non-empty list, it also relates to all the elements in the tail of the list
export
0 tail : {x: a} -> {xs: c} -> Container a c => RelatesToAll rel e (x::xs) -> DecEq a => RelatesToAll rel e xs
tail f prf with (decEq guest x)
  tail f prf | (Yes Refl) = f $ sym $ ConsAddsOne guest xs
  tail f prf | (No guestNEqX) = f $ (sym $ ConsKeepsRest x xs guest guestNEqX) \=> prf

||| If e relates to all the elements in a non-empty list, it also relates to all the elements in the tail of the list
export
0 head : {x: a} -> {xs: c} -> Container a c => RelatesToAll rel e (x::xs) -> DecEq a => rel e x
head f = f $ sym $ ConsAddsOne x xs

0 oneMustBeNonZero : a + b = S n -> Either (Nat # \k => a = S k) (Nat # \k => b = S k)
oneMustBeNonZero {a = 0} {b = 0} prf = void $ SIsNotZ $ sym prf
oneMustBeNonZero {a = 0} {b = (S k)} prf = Right (k # Refl)
oneMustBeNonZero {a = (S k)} {b = b} prf = Left (k # Refl)

||| If e relates to all the elements in the list xs and to all the elements in the list ys then it relates to all the elements in the list xs++ys.
export
0 (++) : {xs, ys: c} -> Container a c => RelatesToAll rel e xs -> RelatesToAll rel e ys -> DecEq a => RelatesToAll rel e (xs++ys)
(++) eXs eYs prf with (oneMustBeNonZero ((sym $ ConcMerges xs ys guest) \=> prf))
  (++) eXs eYs prf | (Left (_ # x)) = eXs x
  (++) eXs eYs prf | (Right (_ # y)) = eYs y
