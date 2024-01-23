module Sorted.IsPermutationOf

import public Control.Relation
import Control.WellFounded
import Data.Nat
import Data.Void
import Decidable.Equality

import public Sorted.Container

%default total


infixr 4 ~@~

%hide Prelude.(::)
%hide Prelude.Nil

namespace IsPermutationOf
  public export
  data IsPermutationOf: Container a c => Rel (c a) where
    Ipo : ((e :a) -> ((e .#. original) @{ct} = (e .#. permutation) @{ct})) -> IsPermutationOf @{ct} original permutation

public export
(~@~) : Container a c => Rel (c a)
original ~@~ permutation = IsPermutationOf original permutation

export
[uninhabitedIsPermutationOfConsNil] {0 x: a} -> {0 xs: c a} -> Container a c => Uninhabited (x::xs ~@~ []) where
    uninhabited (Ipo occ) = void $ uninhabited (((ConsAddsOne x xs) \=> occ {e=x}) \=> (NilIsEmpty x {c}))

export
[uninhabitedIsPermutationOfNilCons] {0 x: a} -> {0 xs: c a} -> Container a c => Uninhabited ([] ~@~ x::xs) where
    uninhabited (Ipo occ) = uninhabited @{uninhabitedIsPermutationOfConsNil {a} {c}} (Ipo $ \e => sym $ occ e)

export
[reflexiveIsPermutationOf] Container a c => Reflexive (c a) (~@~) where
    reflexive = Ipo (\_ => Refl)

export
[transitiveIsPermutationOf] Container a c => Transitive (c a) (~@~) where
    transitive (Ipo occ) (Ipo occ') = Ipo (\e => (occ e) \=> (occ' e))

export
[symmetricIsPermutationOf] Container a c => Symmetric (c a) (~@~) where
  symmetric (Ipo occ) = Ipo (\eInY => sym $ occ eInY)

export
0 PermutationOfCons : {x: a} -> {xs, ys: c a} -> DecEq a => Container a c => x::xs ~@~ x::ys -> xs ~@~ ys
PermutationOfCons (Ipo occ) = Ipo occ' where
    occ' : (e : a) -> e .#. xs = e .#. ys
    occ' e with (decEq e x)
      occ' _ | (Yes Refl) = injective $ ((ConsAddsOne {c} x xs) \=> occ x) \=> (sym $ ConsAddsOne {c} x ys)
      occ' e | (No eNEqX) = (ConsKeepsRest x xs e eNEqX \=> occ e) \=> (sym $ ConsKeepsRest x ys e eNEqX)

export
0 AdditionOfPermutationsCommutes : {xs, ys, p: c a} -> Container a c => p ~@~ (xs++ys) -> DecEq a => p ~@~ (ys++xs)
AdditionOfPermutationsCommutes (Ipo occ) = Ipo occ' where
    occ' : (e : a) -> e .#. p = e .#. (ys ++ xs)
    occ' e = ((occ e \=> (ConcMerges {c} xs ys e)) \=> (plusCommutative (e .#. xs) (e .#. ys))) \=> (sym $ ConcMerges {c} ys xs e)

export
0 (++) : {x, y, z, t: c a} -> Container a c => DecEq a => x ~@~ y -> z ~@~ t -> (x++z) ~@~ (y++t)
(++) (Ipo occ_x_y) (Ipo occ_z_t) = Ipo occ_xz_yt where
    occ_xz_yt : (e : a) -> e .#. (x ++ z) = e .#. (y ++ t)

export
Nil : Container a c => IsPermutationOf {c} [] []
Nil = Ipo (\_ => Refl)

export
PermutationOfNilIsNil : Container a c => {xs: c a} -> IsPermutationOf [] xs -> xs = []
PermutationOfNilIsNil p with (Match xs)
  PermutationOfNilIsNil p | (Left Refl) = Refl
  PermutationOfNilIsNil (Ipo p) | (Right ((x', xs') # x'Xs'EqXs)) =
    void $ SIsNotZ ((ConsAddsOne x' xs') \=> rewrite x'Xs'EqXs in (sym $ p x') \=> (NilIsEmpty {c} x'))

export
(::) : {xs, ys: c a} -> (x: a) -> DecEq a => Container a c => xs ~@~ ys -> x::xs ~@~ x::ys
(::) x (Ipo occ) = Ipo occ' where
    occ': (e : a) -> e .#. (x :: xs) = e .#. (x :: ys)
    occ' e with (decEq e x)
      occ' _ | (Yes Refl) = (sym (ConsAddsOne x xs) \=> cong S (occ x)) \=> ConsAddsOne x ys
      occ' e | (No eNEqX) = (sym (ConsKeepsRest x xs e eNEqX) \=> occ e) \=> ConsKeepsRest x ys e eNEqX

export
tail : {x: a} -> {xs, ys: c a} -> Container a c => x::xs ~@~ x::ys -> DecEq a => xs ~@~ ys
tail (Ipo occ) = Ipo occ' where
    occ' : (e : a) -> e .#. xs = e .#. ys
    occ' e with (decEq e x)
      occ' _ | (Yes Refl) = injective $ (ConsAddsOne x xs \=> occ x) \=> (sym $ ConsAddsOne x ys)
      occ' e | (No eNEqX) = (ConsKeepsRest x xs e eNEqX \=> occ e) \=> (sym $ ConsKeepsRest x ys e eNEqX)

export
pong : Container a c => {0 p: c a -> c a} -> (f: xs ~@~ ys -> p xs ~@~ p ys) ->  xs ~@~ ys -> p xs ~@~ p ys
pong f g = f g

export
0 swapIsPermutation : {x,y: a} -> DecEq a => Container a c => (e: a) -> e .#. (Container.(::) {c} x (Container.(::) y Container.Nil)) = e .#. (Container.(::) {c} y (Container.(::) x Container.Nil))
swapIsPermutation e with (decEq e x, decEq e y)
  swapIsPermutation e | ((Yes Refl), Yes Refl) = Refl
  swapIsPermutation e | ((Yes Refl), No eNEqY) = sym ((cong S $ ConsKeepsRest {c} y [] e eNEqY) \=> (ConsAddsOne {c} e [y])) \=> (ConsAddsOne {c} e [] \=> (ConsKeepsRest {c} y [e] e eNEqY))
  swapIsPermutation e | ((No eNEqX), Yes Refl) = sym (ConsKeepsRest {c} x [e] e eNEqX) \=> ((sym (ConsAddsOne {c} e []) \=> (cong S (ConsKeepsRest {c} x [] e eNEqX))) \=> ConsAddsOne {c} e [x])
  swapIsPermutation e | ((No eNEqX), No eNEqY) = sym ((sym $ NilIsEmpty {c} e) \=> (ConsKeepsRest {c} y [] e eNEqY \=> (ConsKeepsRest {c} x [y] e eNEqX))) \=> ((sym (NilIsEmpty {c} e) \=> (ConsKeepsRest {c} x [] e eNEqX)) \=> ConsKeepsRest {c} y [x] e eNEqY)

export
0 shiftPermutation : {0 y: a} -> {0 xs, ys, ys': c a} -> DecEq a => Container a c => IsPermutationOf {c} {a} ys (y::ys') -> IsPermutationOf {c} {a} (xs++ys) (y::(xs++ys'))
shiftPermutation x = (
  replace {p = IsPermutationOf (xs ++ ys)}
    (ConcReduces y ys' xs)
    (AdditionOfPermutationsCommutes $ reflexive @{reflexiveIsPermutationOf} {x=xs} ++ x)
      \=> y :: (AdditionOfPermutationsCommutes $ reflexive @{reflexiveIsPermutationOf} {x=ys' ++ xs})
      ) @{transitiveIsPermutationOf}

export
0 PermutationHasSameSize : DecEq a => Container a c => {xs, ys: c a} -> xs ~@~ ys -> size @{ContainerSized} xs = size @{ContainerSized} ys
PermutationHasSameSize ipo with (sizeAccessible @{ContainerSized} xs)
  PermutationHasSameSize ipo | acc with (Match xs)
    PermutationHasSameSize ipo | acc | (Left Refl) with (PermutationOfNilIsNil ipo)
      PermutationHasSameSize ipo | acc | (Left Refl) | Refl = Refl
    PermutationHasSameSize ipo | Access acc | (Right ((h, t) # Refl)) with (findFirst h ys)
      PermutationHasSameSize (Ipo f) | Access acc | (Right ((h, t) # Refl)) | Left l = void $ SIsNotZ (ConsAddsOne h t \=> f h \=> l)
      PermutationHasSameSize ipo | Access acc | (Right ((h, t) # Refl)) | Right ((l, r) # (h∉l, Refl)) =
          SizedCons \=>
          cong S (PermutationHasSameSize (tail ((ipo \=> shiftPermutation (reflexive @{reflexiveIsPermutationOf})) @{transitiveIsPermutationOf})) | acc _ $ eqLTE $ sym SizedCons) \=>
          cong S (SizedConc l r) \=>
          plusSuccRightSucc _ _ \=>
          cong (size @{ContainerSized} l +) (sym SizedCons) \=>
          sym (SizedConc l (h::r))
