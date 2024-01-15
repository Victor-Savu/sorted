module Sorted.IsPermutationOf

import public Control.Relation
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
    uninhabited (Ipo occ) = void $ uninhabited (((ConsAddsOne x xs) `transitive` occ {e=x}) `transitive` (NilIsEmpty x {c}))

export
[uninhabitedIsPermutationOfNilCons] {0 x: a} -> {0 xs: c a} -> Container a c => Uninhabited ([] ~@~ x::xs) where
    uninhabited (Ipo occ) = uninhabited @{uninhabitedIsPermutationOfConsNil {a} {c}} (Ipo $ \e => sym $ occ e)

export
[reflexiveIsPermutationOf] Container a c => Reflexive (c a) (~@~) where
    reflexive = Ipo (\_ => Refl)

export
[transitiveIsPermutationOf] Container a c => Transitive (c a) (~@~) where
    transitive (Ipo occ) (Ipo occ') = Ipo (\e => (occ e) `transitive` (occ' e))

export
[symmetricIsPermutationOf] Container a c => Symmetric (c a) (~@~) where
  symmetric (Ipo occ) = Ipo (\eInY => sym $ occ eInY)

export
0 PermutationOfCons : {x: a} -> {xs, ys: c a} -> DecEq a => Container a c => x::xs ~@~ x::ys -> xs ~@~ ys
PermutationOfCons (Ipo occ) = Ipo occ' where
    occ' : (e : a) -> e .#. xs = e .#. ys
    occ' e with (decEq e x)
      occ' _ | (Yes Refl) = injective $ ((ConsAddsOne {c} x xs) `transitive` occ x) `transitive` (sym $ ConsAddsOne {c} x ys)
      occ' e | (No eNEqX) = (ConsKeepsRest x xs e eNEqX `transitive` occ e) `transitive` (sym $ ConsKeepsRest x ys e eNEqX)

export
0 AdditionOfPermutationsCommutes : {xs, ys, p: c a} -> Container a c => p ~@~ (xs++ys) -> DecEq a => p ~@~ (ys++xs)
AdditionOfPermutationsCommutes (Ipo occ) = Ipo occ' where
    occ' : (e : a) -> e .#. p = e .#. (ys ++ xs)
    occ' e = ((occ e `transitive` (ConcMerges {c} xs ys e)) `transitive` (plusCommutative (e .#. xs) (e .#. ys))) `transitive` (sym $ ConcMerges {c} ys xs e)

export
0 (++) : {x, y, z, t: c a} -> Container a c => DecEq a => x ~@~ y -> z ~@~ t -> (x++z) ~@~ (y++t)
(++) (Ipo occ_x_y) (Ipo occ_z_t) = Ipo occ_xz_yt where
    occ_xz_yt : (e : a) -> e .#. (x ++ z) = e .#. (y ++ t)
--     occ_xz_yt e = (ConcMerges {c} x z e `transitive` cong2 (+) (occ_x_y e) (occ_z_t e)) `transitive` (sym $ ConcMerges {c} y t e)

export
Nil : Container a c => IsPermutationOf {c} [] []
Nil = Ipo (\_ => Refl)

export
0 (::) : {0 xs, ys: c a} -> (x: a) -> DecEq a => Container a c => xs ~@~ ys -> x::xs ~@~ x::ys
(::) x (Ipo occ) = Ipo occ' where
    occ': (e : a) -> e .#. (x :: xs) = e .#. (x :: ys)
    occ' e with (decEq e x)
      occ' _ | (Yes Refl) = (sym (ConsAddsOne x xs) `transitive` cong S (occ x)) `transitive` ConsAddsOne x ys
      occ' e | (No eNEqX) = (sym (ConsKeepsRest x xs e eNEqX) `transitive` occ e) `transitive` ConsKeepsRest x ys e eNEqX

export
0 tail : {x: a} -> {0 xs, ys: c a} -> Container a c => x::xs ~@~ x::ys -> DecEq a => xs ~@~ ys
tail (Ipo occ) = Ipo occ' where
    occ' : (e : a) -> e .#. xs = e .#. ys
    occ' e with (decEq e x)
      occ' _ | (Yes Refl) = injective $ (ConsAddsOne x xs `transitive` occ x) `transitive` (sym $ ConsAddsOne x ys)
      occ' e | (No eNEqX) = (ConsKeepsRest x xs e eNEqX `transitive` occ e) `transitive` (sym $ ConsKeepsRest x ys e eNEqX)

export
0 swapIsPermutation : {x,y: a} -> DecEq a => Container a c => (e: a) -> e .#. (Container.(::) {c} x (Container.(::) y Container.Nil)) = e .#. (Container.(::) {c} y (Container.(::) x Container.Nil))
swapIsPermutation e with (decEq e x, decEq e y)
  swapIsPermutation e | ((Yes Refl), Yes Refl) = Refl
  swapIsPermutation e | ((Yes Refl), No eNEqY) = sym ((cong S $ ConsKeepsRest {c} y [] e eNEqY) `transitive` (ConsAddsOne {c} e [y])) `transitive` (ConsAddsOne {c} e [] `transitive` (ConsKeepsRest {c} y [e] e eNEqY))
  swapIsPermutation e | ((No eNEqX), Yes Refl) = sym (ConsKeepsRest {c} x [e] e eNEqX) `transitive` ((sym (ConsAddsOne {c} e []) `transitive` (cong S (ConsKeepsRest {c} x [] e eNEqX))) `transitive` ConsAddsOne {c} e [x])
  swapIsPermutation e | ((No eNEqX), No eNEqY) = sym ((sym $ NilIsEmpty {c} e) `transitive` (ConsKeepsRest {c} y [] e eNEqY `transitive` (ConsKeepsRest {c} x [y] e eNEqX))) `transitive` ((sym (NilIsEmpty {c} e) `transitive` (ConsKeepsRest {c} x [] e eNEqX)) `transitive` ConsKeepsRest {c} y [x] e eNEqY)