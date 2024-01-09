module Sorted.IsPermutationOf

import public Control.Relation
import public Data.Nat
import public Data.Void
import public Decidable.Equality

import Sorted.Occurs

%default total


infixr 4 ~@~

namespace IsPermutationOf
  public export
  data IsPermutationOf: Rel (List a) where
    Ipo : (occ: {e: a} -> {0 n: Nat} -> Occurs e n original -> Occurs e n permutation) -> IsPermutationOf original permutation

public export
(~@~) : Rel (List a)
original ~@~ permutation = IsPermutationOf original permutation

public export
[uninhabitedIsPermutationOfConsNil] {0 x: a} -> DecEq a => Uninhabited (x::xs ~@~ []) where
    uninhabited (Ipo occ) = absurdity @{uninhabitedOccursAtLeastOnceInNil} $ occ $ Here $ snd $ countOccurrences x xs

public export
[uninhabitedIsPermutationOfNilCons] {0 x: a} -> Uninhabited ([] ~@~ x::xs) where
    uninhabited (Ipo occ) = absurdity @{uninhabitedOccursZeroTimesWhenHeadMatches} $ occ {e=x} Nowhere

public export
[uninhabitedIsPermutationOfConsConsXsConsNil] {x, x', y: a} -> {xs: List a} -> DecEq a => Uninhabited (x::x'::xs ~@~ [y]) where
    uninhabited (Ipo occ) with (decEq x x')
      uninhabited (Ipo occ) | (Yes Refl) with (countOccurrences x xs)
        uninhabited (Ipo occ) | (Yes Refl) | (n ** xInXs) with (occ $ Here $ Here xInXs)
          uninhabited (Ipo occ) | (Yes Refl) | (n ** xInXs) | (Here z) = absurdity @{uninhabitedOccursAtLeastOnceInNil} z
          uninhabited (Ipo occ) | (Yes Refl) | (n ** xInXs) | (There z _) = absurdity @{uninhabitedOccursAtLeastOnceInNil} z
      uninhabited (Ipo occ) | (No xNEqX') with (decEq x y)
        uninhabited (Ipo occ) | (No xNEqX') | (Yes Refl) with (countOccurrences x' xs)
          uninhabited (Ipo occ) | (No xNEqX') | (Yes Refl) | (_ ** x'InXs) with (occ $ There (Here x'InXs) (xNEqX' . \q => sym q))
            uninhabited (Ipo occ) | (No xNEqX') | (Yes Refl) | (_ ** x'InXs) | (Here Nowhere) = void $ xNEqX' Refl
            uninhabited (Ipo occ) | (No xNEqX') | (Yes Refl) | (_ ** x'InXs) | (There z _) = absurdity @{uninhabitedOccursAtLeastOnceInNil} z
        uninhabited (Ipo occ) | (No xNEqX') | (No xNEqY) with (countOccurrences x xs)
          uninhabited (Ipo occ) | (No xNEqX') | (No xNEqY) | (_ ** xInXs) with (occ $ Here $ There xInXs xNEqX')
            uninhabited (Ipo occ) | (No xNEqX') | (No xNEqY) | (_ ** xInXs) | (Here Nowhere) = void $ xNEqY Refl
            uninhabited (Ipo occ) | (No xNEqX') | (No xNEqY) | (_ ** xInXs) | (There z _) = absurdity @{uninhabitedOccursAtLeastOnceInNil} z

public export
[reflexiveIsPermutationOf] Reflexive (List a) (~@~) where
    reflexive = Ipo id

public export
[transitiveIsPermutationOf] DecEq a => Transitive (List a) (~@~) where
    transitive (Ipo occ) (Ipo occ') = Ipo (occ' . occ)

public export
[symmetricIsPermutationOf] DecEq a => Symmetric (List a) (~@~) where
    symmetric (Ipo occ) = Ipo occ_x_y where
      occ_x_y : {e: a} -> Occurs e n y -> Occurs e n x
      occ_x_y eInY with (countOccurrences e x)
        occ_x_y eInY | (_ ** eInX) with (occ eInX ..=.. eInY)
          occ_x_y eInY | (_ ** eInX) | Refl = eInX

public export
PermutationOfNilIsNil : {xs: List a} -> [] ~@~ xs -> DecEq a => xs = []
PermutationOfNilIsNil {xs = []} (Ipo occ) = Refl
PermutationOfNilIsNil {xs = (x :: xs)} (Ipo occ) = absurdity $ Here (snd $ countOccurrences x xs) ..=.. occ Nowhere

public export
SingletonPermutationIsIdentity : {x, y: a} -> DecEq a => [x] ~@~ [y] -> [x] = [y]
SingletonPermutationIsIdentity (Ipo occ) with (decEq x y)
  SingletonPermutationIsIdentity (Ipo occ) | (Yes prf) = cong (\e => [e]) prf
  SingletonPermutationIsIdentity (Ipo occ) | (No contra) with (occ $ Here Nowhere)
    SingletonPermutationIsIdentity (Ipo occ) | (No contra) | (Here z) = void $ contra Refl
    SingletonPermutationIsIdentity (Ipo occ) | (No contra) | (There z f) = absurdity @{uninhabitedOccursAtLeastOnceInNil} z

public export
PermutationOfCons : {x: a} -> {0 xs, ys: List a} -> DecEq a => x::xs ~@~ x::ys ->  xs ~@~ ys
PermutationOfCons (Ipo occ) = Ipo occ_xs_ys where
    occ_xs_ys : {e: a} -> Occurs e m xs -> Occurs e m ys
    occ_xs_ys eInXs with (decEq x e)
      occ_xs_ys eInXs | (Yes Refl) = case occ $ Here $ eInXs of
        (Here y) => y
        (There y f) => void $ f Refl
      occ_xs_ys eInXs | (No contra) = case occ $ There eInXs (contra . \shoo => sym shoo) of
        (Here y) => void $ contra Refl
        (There y f) => y

public export
AdditionOfPermutationsCommutes : {xs, ys, p: List a} -> p ~@~ (xs++ys) -> DecEq a => p ~@~ (ys++xs)
AdditionOfPermutationsCommutes (Ipo occ) = Ipo aop where
    aop : {e: a} -> Occurs e n p -> Occurs e n (ys ++ xs)
    aop eInP with (countOccurrences e xs, countOccurrences e ys)
      aop eInP | ((n' ** eInXs), (n'' ** eInYs)) =
        replace {p = \q => Occurs e q (ys ++ xs)}
          ((eInXs + eInYs) ..=.. occ eInP) $
            replace {p = \q => Occurs e q (ys ++ xs)} (plusCommutative n'' n') (eInYs + eInXs)

public export
(++) : {x, y, z, t: List a} -> DecEq a => x ~@~ y -> z ~@~ t -> (x++z) ~@~ (y++t)
(++) (Ipo occ_x_y) (Ipo occ_z_t) = Ipo occ_xz_yt where
    occ_xz_yt : {e: a} -> Occurs e n (x ++ z) -> Occurs e n (y ++ t)
    occ_xz_yt e_in_xz =
      let
        (cx ** px) = countOccurrences e x
        (cy ** py) = countOccurrences e y
        (cz ** pz) = countOccurrences e z
        (ct ** pt) = countOccurrences e t
      in replace {p = \q => Occurs e q (y ++ t)}
        ((cong2 (+) (py ..=.. occ_x_y px) (pt ..=.. occ_z_t pz)) `transitive` ((px + pz) ..=.. e_in_xz))
        (py + pt)

public export
Nil : IsPermutationOf [] []
Nil = Ipo id

public export
(::) : {0 xs, ys: List a} -> (x: a) -> xs ~@~ ys -> x::xs ~@~ x::ys
(::) x (Ipo occ) = Ipo occ_xxs_xys where
    occ_xxs_xys : {e: a} -> Occurs e n (x :: xs) -> Occurs e n (x :: ys)
    occ_xxs_xys (Here y) = Here (occ y)
    occ_xxs_xys (There y f) = There (occ y) f

public export
tail : {x: a} -> x::xs ~@~ x::ys -> DecEq a => xs ~@~ ys
tail (Ipo occ) = Ipo occ_xs_ys where
    occ_xs_ys : {e: a} -> Occurs e n xs -> Occurs e n ys
    occ_xs_ys xInXs with (decEq e x)
      occ_xs_ys xInXs | (Yes Refl) = case occ $ Here xInXs of
        (Here xInYs) => xInYs
        (There y f) => void $ f Refl
      occ_xs_ys xInXs | (No eNEqX) = case occ $ There xInXs eNEqX of
        (Here y) => void $ eNEqX Refl
        (There eInYs _) => eInYs
