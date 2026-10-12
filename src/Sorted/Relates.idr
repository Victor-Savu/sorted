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
RelatesToAll relates socialButterfly party = {guest: a} -> {n: Nat} -> (0 guest∈party: guest .#. party = (S n)) -> relates socialButterfly guest

export infixr 4 -@->

||| If x relates to all the elements of xs , then it relates to any permutation ys of the elements of xs
export
(-@->) : {x: a} -> {xs, ys: c} -> Container a c => RelatesToAll rel x xs -> (xs ~@~ ys) -> RelatesToAll rel x ys
(-@->) f (Ipo g) y = f (g guest \=> y)


%hide Prelude.(::)
%hide Prelude.Nil
%hide Stream.(::)

export
Nil : {0 x: a} -> Container a c => RelatesToAll {c} rel x Container.Nil
Nil prf with (sym prf \=> ∀x‥x⋕【】≐0)
  Nil prf | _ impossible

||| If x relates to y and x also relates to all the elements of the list xs then x relates to all the elements of y::xs
export
(::) : {y: a} -> {rel: Rel a} -> {xs: c} -> rel x y -> Container a c => RelatesToAll rel x xs -> RelatesToAll rel x (y::xs)
(::) relXY f prf with (decEq guest y)
  (::) relXGuest f prf | (Yes Refl) = relXGuest
  (::) relXY f prf | (No guestNEqY) = f $ ConsKeepsRest guestNEqY \=> prf

||| If e relates to all the elements in a non-empty list, it also relates to all the elements in the tail of the list
export
tail : {x: a} -> {xs: c} -> Container a c => RelatesToAll rel e (x::xs) -> RelatesToAll rel e xs
tail f prf with (decEq guest x)
  tail f prf | (Yes Refl) = f $ sym $ ConsAddsOne
  tail f prf | (No guestNEqX) = f $ (sym $ ConsKeepsRest guestNEqX) \=> prf

||| If e relates to all the elements in a non-empty list, it also relates to all the elements in the tail of the list
export
head : {x: a} -> {xs: c} -> Container a c => RelatesToAll rel e (x::xs) -> rel e x
head f = f $ sym $ ConsAddsOne

oneMustBeNonZero : {a, b: Nat} -> a + b = S n -> (k:Nat ** Either (a = S k) (b = S k))
oneMustBeNonZero {a = 0} {b = 0} prf = void $ SIsNotZ $ sym prf
oneMustBeNonZero {a = 0} {b = (S k)} prf = (k ** Right Refl)
oneMustBeNonZero {a = (S k)} {b = b} prf = (k ** Left Refl)

||| If e relates to all the elements in the list xs and to all the elements in the list ys then it relates to all the elements in the list xs++ys.
export
0 (++) : {xs, ys: c} -> Container a c => RelatesToAll rel e xs -> RelatesToAll rel e ys -> RelatesToAll rel e (xs++ys)
(++) e❤xs e❤ys guest∈xs⨢⨢ys with (oneMustBeNonZero (sym ConcAddsCounts \=> guest∈xs⨢⨢ys))
  (++) e❤xs e❤ys guest∈xs⨢⨢ys | (_ ** (Left guest∈xs)) = e❤xs guest∈xs
  (++) e❤xs e❤ys guest∈xs⨢⨢ys | (_ ** (Right guest∈ys)) = e❤ys guest∈ys
