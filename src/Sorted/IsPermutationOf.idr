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
  data IsPermutationOf: Container a c => Rel c where
    Ipo : ((e :a) -> ((e .#. original) @{ct} = (e .#. permutation) @{ct})) -> IsPermutationOf @{ct} original permutation

public export
(~@~) : Container a c => Rel c
original ~@~ permutation = IsPermutationOf original permutation

export
[uninhabitedIsPermutationOfConsNil] {0 x: a} -> {0 xs: c} -> Container a c => Uninhabited (x::xs ~@~ []) where
    uninhabited (Ipo occ) = void $ uninhabited ((ConsAddsOne \=> occ {e=x}) \=> NilIsEmpty)

export
[uninhabitedIsPermutationOfNilCons] {0 x: a} -> {0 xs: c} -> Container a c => Uninhabited ([] ~@~ x::xs) where
    uninhabited (Ipo occ) = uninhabited @{uninhabitedIsPermutationOfConsNil {a} {c}} (Ipo $ \e => sym $ occ e)

export
[reflexiveIsPermutationOf] Container a c => Reflexive c (~@~) where
    reflexive = Ipo (\_ => Refl)

export
[transitiveIsPermutationOf] Container a c => Transitive c (~@~) where
    transitive (Ipo occ) (Ipo occ') = Ipo (\e => (occ e) \=> (occ' e))

export
[symmetricIsPermutationOf] Container a c => Symmetric c (~@~) where
  symmetric (Ipo occ) = Ipo (\eInY => sym $ occ eInY)

export
0 PermutationOfCons : {x: a} -> {xs, ys: c} -> DecEq a => Container a c => x::xs ~@~ x::ys -> xs ~@~ ys
PermutationOfCons (Ipo occ) = Ipo occ' where
    occ' : (e : a) -> e .#. xs = e .#. ys
    occ' e with (decEq e x)
      occ' _ | (Yes Refl) = injective $ (ConsAddsOne \=> occ x) \=> (sym $ ConsAddsOne)
      occ' e | (No eNEqX) = (ConsKeepsRest eNEqX \=> occ e) \=> (sym $ ConsKeepsRest eNEqX)

export
0 AdditionOfPermutationsCommutes : {xs, ys, p: c} -> Container a c => p ~@~ (xs++ys) -> DecEq a => p ~@~ (ys++xs)
AdditionOfPermutationsCommutes (Ipo occ) = Ipo occ' where
    occ' : (e : a) -> e .#. p = e .#. (ys ++ xs)
    occ' e = ((occ e \=> (ConcMerges {c} xs ys e)) \=> (plusCommutative (e .#. xs) (e .#. ys))) \=> (sym $ ConcMerges {c} ys xs e)

export
0 (++) : {x, y, z, t: c} -> Container a c => DecEq a => x ~@~ y -> z ~@~ t -> (x++z) ~@~ (y++t)
(++) (Ipo occ_x_y) (Ipo occ_z_t) = Ipo occ_xz_yt where
    occ_xz_yt : (e : a) -> e .#. (x ++ z) = e .#. (y ++ t)

export
Nil : Container a c => IsPermutationOf {c} [] []
Nil = Ipo (\_ => Refl)

export
PermutationOfNilIsNil : Container a c => {xs: c} -> IsPermutationOf [] xs -> xs = []
PermutationOfNilIsNil p with (Match xs)
  PermutationOfNilIsNil p | (Left Refl) = Refl
  PermutationOfNilIsNil (Ipo p) | (Right ((x', xs') # x'Xs'EqXs)) =
    void $ SIsNotZ (ConsAddsOne {c} \=> ?choo \=> NilIsEmpty {c})

export
0 (::) : {xs, ys: c} -> (x: a) -> DecEq a => Container a c => xs ~@~ ys -> x::xs ~@~ x::ys
(::) x (Ipo occ) = Ipo occ' where
    occ': (e : a) -> e .#. (x :: xs) = e .#. (x :: ys)
    occ' e with (decEq e x)
      occ' _ | (Yes Refl) = (sym ConsAddsOne \=> cong S (occ x)) \=> ConsAddsOne
      occ' e | (No eNEqX) = (sym (ConsKeepsRest eNEqX) \=> occ e) \=> ConsKeepsRest eNEqX

export
0 tail : {x: a} -> {xs, ys: c} -> Container a c => x::xs ~@~ x::ys -> DecEq a => xs ~@~ ys
tail (Ipo occ) = Ipo occ' where
    occ' : (e : a) -> e .#. xs = e .#. ys
    occ' e with (decEq e x)
      occ' _ | (Yes Refl) = injective $ (ConsAddsOne \=> occ x) \=> sym ConsAddsOne
      occ' e | (No eNEqX) = (ConsKeepsRest eNEqX \=> occ e) \=> (sym $ ConsKeepsRest eNEqX)

export
pong : Container a c => {0 p: c -> c} -> (f: xs ~@~ ys -> p xs ~@~ p ys) ->  xs ~@~ ys -> p xs ~@~ p ys
pong f g = f g

export
0 swapIsPermutation : {x,y: a} -> DecEq a => Container a c => (e: a) -> e .#. (Container.(::) {c} x (Container.(::) y Container.Nil)) = e .#. (Container.(::) {c} y (Container.(::) x Container.Nil))
swapIsPermutation e with (decEq e x, decEq e y)
  swapIsPermutation e | ((Yes Refl), Yes Refl) = Refl
  swapIsPermutation e | ((Yes Refl), No eNEqY) = sym ((cong S $ ConsKeepsRest eNEqY) \=> ConsAddsOne) \=> ConsAddsOne \=> (ConsKeepsRest eNEqY)
  swapIsPermutation e | ((No eNEqX), Yes Refl) = sym (ConsKeepsRest eNEqX) \=> sym ConsAddsOne \=> (cong S (ConsKeepsRest eNEqX)) \=> ConsAddsOne
  swapIsPermutation e | ((No eNEqX), No eNEqY) = sym (ConsKeepsRest eNEqY \=> ConsKeepsRest eNEqX) \=> ConsKeepsRest eNEqX \=> ConsKeepsRest eNEqY

export
0 shiftPermutation : {0 y: a} -> {0 xs, ys, ys': c} -> DecEq a => Container a c => IsPermutationOf {c} {a} ys (y::ys') -> IsPermutationOf {c} {a} (xs++ys) (y::(xs++ys'))
shiftPermutation x = (
  replace {p = IsPermutationOf (xs ++ ys)}
    ConcReduces
    (AdditionOfPermutationsCommutes $ reflexive @{reflexiveIsPermutationOf} {x=xs} ++ x)
      \=> y :: (AdditionOfPermutationsCommutes $ reflexive @{reflexiveIsPermutationOf} {x=ys' ++ xs})
      ) @{transitiveIsPermutationOf}

export
0 PermutationHasSameSize : DecEq a => Container a c => {xs, ys: c} -> xs ~@~ ys -> size @{ContainerSized} xs = size @{ContainerSized} ys
PermutationHasSameSize ipo with (sizeAccessible @{ContainerSized} xs)
  PermutationHasSameSize ipo | acc with (Match xs)
    PermutationHasSameSize ipo | acc | (Left Refl) with (PermutationOfNilIsNil ipo)
      PermutationHasSameSize ipo | acc | (Left Refl) | Refl = Refl
    PermutationHasSameSize ipo | Access acc | (Right ((h, t) # Refl)) with (findFirst h ys)
      PermutationHasSameSize (Ipo f) | Access acc | (Right ((h, t) # Refl)) | Left l = void $ SIsNotZ (ConsAddsOne \=> f h \=> l)
      PermutationHasSameSize ipo | Access acc | (Right ((h, t) # Refl)) | Right ((l, r) # (h∉l, Refl)) =
          SizedCons \=>
          cong S (PermutationHasSameSize (tail ((ipo \=> shiftPermutation (reflexive @{reflexiveIsPermutationOf})) @{transitiveIsPermutationOf})) | acc _ $ eqLTE $ sym SizedCons) \=>
          cong S (SizedConc l r) \=>
          plusSuccRightSucc _ _ \=>
          cong (size @{ContainerSized} l +) (sym SizedCons) \=>
          sym (SizedConc l (h::r))
