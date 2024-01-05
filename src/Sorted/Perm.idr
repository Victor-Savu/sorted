module Sorted.Perm

import public Control.Relation
import public Data.Nat
import public Data.Void
import public Decidable.Equality

import Sorted.Occurs

%default total


infixr 4 ~@~

public export
0 (~@~) : Rel (List a)
original ~@~ permutation = {anElement: a} -> {occurrenciesInOriginal, occurrenciesInPermutation: Nat} -> (occursInOriginal: Occurs anElement occurrenciesInOriginal original) -> (occursInPermutation: Occurs anElement occurrenciesInPermutation permutation) -> occurrenciesInOriginal = occurrenciesInPermutation


public export
[uninhabitedIsPermutationOfConsNil] {0 x: a} -> DecEq a => Uninhabited (x::xs ~@~ []) where
    uninhabited isPermutationOfConsNil = absurdity $ isPermutationOfConsNil (Here $ let (0 ** xInXsPrf) = countOccurrences x xs in xInXsPrf) Nowhere

public export
[uninhabitedIsPermutationOfNilCons] {0 x: a} -> DecEq a => Uninhabited ([] ~@~ x::xs) where
    uninhabited isPermutationOfNilCons = absurdity $ isPermutationOfNilCons Nowhere (Here $ let (0 ** xInXsPrf) = countOccurrences x xs in xInXsPrf)

public export
[uninhabitedIsPermutationOfConsConsXsConsNil] {x, x', y: a} -> {xs: List a} -> DecEq a => Uninhabited (x::x'::xs ~@~ [y]) where
  uninhabited ipo with (decEq x x')
    uninhabited ipo | (Yes xEqX') with (decEq x y)
      uninhabited ipo | (Yes xEqX') | (Yes xEqY) =
        let 
          allAboutX = replace
            {p = \yyy => {anElement: a} -> {occurrenciesInOriginal, occurrenciesInPermutation: Nat} -> Occurs anElement occurrenciesInOriginal (x :: (yyy :: xs)) -> Occurs anElement occurrenciesInPermutation [x] -> occurrenciesInOriginal = occurrenciesInPermutation}
            (sym xEqX') $
            replace
            {p = \yyy => {anElement: a} -> {occurrenciesInOriginal, occurrenciesInPermutation: Nat} -> Occurs anElement occurrenciesInOriginal (x :: (x' :: xs)) -> Occurs anElement occurrenciesInPermutation [yyy] -> occurrenciesInOriginal = occurrenciesInPermutation}
            (sym xEqY)
            ipo
          (_ ** xInXsPrf) = countOccurrences x xs
          succSuccEqOne = allAboutX (Here $ Here xInXsPrf) (Here Nowhere)
        in uninhabited succSuccEqOne
      uninhabited ipo | (Yes xEqX') | (No xNEqY) =
        let
          allAboutX = replace
            {p = \yyy => {anElement: a} -> {occurrenciesInOriginal, occurrenciesInPermutation: Nat} -> Occurs anElement occurrenciesInOriginal (x :: (yyy :: xs)) -> Occurs anElement occurrenciesInPermutation [y] -> occurrenciesInOriginal = occurrenciesInPermutation}
            (sym xEqX')
            ipo
          (_ ** xInXsPrf) = countOccurrences x xs
          succSuccEqZero = allAboutX (Here $ Here xInXsPrf) (There Nowhere xNEqY)
        in uninhabited succSuccEqZero
    uninhabited ipo | (No xNEqX') with (decEq x y)
      uninhabited ipo | (No xNEqX') | (No xNEqY) =
        let
          (xInXs ** xInXsPrf) = countOccurrences x xs
          succEqZero = ipo (Here $ There xInXsPrf xNEqX') (There Nowhere xNEqY)
        in uninhabited succEqZero
      uninhabited ipo | (No xNEqX') | (Yes xEqY) with (decEq x' y)
        uninhabited ipo | (No xNEqX') | (Yes xEqY) | (Yes x'EqY) = xNEqX' $ transitive xEqY (sym x'EqY)
        uninhabited ipo | (No xNEqX') | (Yes xEqY) | (No x'NEqY) =
          let
            (x'InXs ** x'InXsPrf) = countOccurrences x' xs
            sym' = sym {x=x} {y=x'}
            x'NeqX : (x' = x -> Void) = \prf => let symprf = sym prf in xNEqX' symprf
            succEqZero = ipo (There (Here x'InXsPrf) x'NeqX) (There Nowhere x'NEqY)
          in uninhabited succEqZero

public export
[reflexiveIsPermutationOf] Reflexive (List a) (~@~) where
    reflexive Nowhere Nowhere = Refl
    reflexive (There y f) (Here z) = void $ f Refl
    reflexive (There y f) (There z g) = reflexive @{reflexiveIsPermutationOf} y z
    reflexive (Here _) Nowhere impossible
    reflexive (Here pm) (Here pn) = cong S $ reflexive @{reflexiveIsPermutationOf} pm pn
    reflexive (Here _) (There _ f) = void $ f Refl

public export
[transitiveIsPermutationOf] DecEq a => Transitive (List a) (~@~) where
    transitive {x=original} {y=permutation} {z=anotherPermutation} isPermutationOP isPermutationPA occursInOriginal occursInAnother =
      let
        (_ ** occursInPermutation) = countOccurrences anElement permutation
      in transitive (isPermutationOP occursInOriginal occursInPermutation) (isPermutationPA occursInPermutation occursInAnother)

public export
[symmetricIsPermutationOf] Symmetric (List a) (~@~) where
    symmetric isPermutation occurrsInPermutation occurrsInOriginal= sym $ isPermutation occurrsInOriginal occurrsInPermutation

public export
SingletonPermutationIsIdentity : {x, y: a} -> DecEq a => [x] ~@~ [y] -> [x] = [y]
SingletonPermutationIsIdentity isPermutationOfXY with (decEq x y)
  SingletonPermutationIsIdentity isPermutationOfXY | (Yes prf) = cong (\e => [e]) prf
  SingletonPermutationIsIdentity isPermutationOfXY | (No contra) with (isPermutationOfXY (Here Nowhere) (There Nowhere contra))
    SingletonPermutationIsIdentity isPermutationOfXY | (No contra) | _ impossible

public export
PermutationOfCons : {x: a} -> {0 xs, ys: List a} -> DecEq a => x::xs ~@~ x::ys ->  xs ~@~ ys
PermutationOfCons f occursInOriginal occursInPermutation with (decEq anElement x)
  PermutationOfCons f occursInOriginal occursInPermutation | (Yes anElementEqX) = cong pred $ f (Here $ rewrite sym anElementEqX in occursInOriginal) (Here $ rewrite sym anElementEqX in occursInPermutation)
  PermutationOfCons f occursInOriginal occursInPermutation | (No anElementNEqX) = f (There occursInOriginal anElementNEqX) (There occursInPermutation anElementNEqX)

public export
AdditionOfPermutationsCommutes : {xs, ys, p: List a} -> p ~@~ (xs++ys) -> DecEq a => p ~@~ (ys++xs)
AdditionOfPermutationsCommutes f occursInOriginal occursInPermutation = let
    (eInXs ** eInXsPrf) = countOccurrences anElement xs
    (eInYs ** eInYsPrf) = countOccurrences anElement ys
    eInYsXsPrf = eInYsPrf + eInXsPrf
    ysXsEqP = sym $ OccursTheSameNumberOfTimes occursInPermutation eInYsXsPrf
    xsYsEqYsXs = plusCommutative eInXs eInYs
    oEqXsYs = f occursInOriginal (eInXsPrf + eInYsPrf)
  in (oEqXsYs `transitive` xsYsEqYsXs) `transitive` ysXsEqP

public export
(++) : {x, y, z, t: List a} -> DecEq a => x ~@~ y -> z ~@~ t -> (x++z) ~@~ (y++t)
(++) {anElement=e} xy zt occursInOriginal occursInPermutation =
  let
    (cx ** px) = countOccurrences e x
    (cy ** py) = countOccurrences e y
    (cz ** pz) = countOccurrences e z
    (ct ** pt) = countOccurrences e t
    pxz = px + pz
    pyt = py + pt
    exy = xy px py
    ezt  = zt pz pt
    bridge = cong2 (+) exy ezt
    consider = OccursTheSameNumberOfTimes occursInOriginal pxz 
    consider' = OccursTheSameNumberOfTimes occursInPermutation pyt
  in (consider `transitive` bridge) `transitive` (sym consider')

public export
(::) : {0 xs, ys: List a} -> (x: a) -> xs ~@~ ys -> DecEq a => x::xs ~@~ x::ys
(::) x f (Here y) (Here z) = cong S $ f y z
(::) x f (Here y) (There g ne) = void $ ne Refl
(::) x f (There y g) (Here z) = void $ g Refl
(::) x f (There y g) (There z f1) = f y z

public export
tail : {x: a} -> x::xs ~@~ x::ys -> DecEq a => xs ~@~ ys
tail permXY occursInOriginal occursInPermutation with (decEq anElement x)
  tail permXY occursInOriginal occursInPermutation | (Yes anElementEqX) =
    let
      xInXXs = replace {p = \e => Occurs e (S occurrenciesInOriginal) (e::xs) } anElementEqX (anElement::occursInOriginal)
      yInYYs = replace {p = \e => Occurs e (S occurrenciesInPermutation) (e::ys) } anElementEqX (anElement::occursInPermutation)
      anElementInXXs = replace {p = \e => Occurs e (S occurrenciesInOriginal) (x::xs) } (sym anElementEqX) xInXXs
      anElementInYYs = replace {p = \e => Occurs e (S occurrenciesInPermutation) (x::ys) } (sym anElementEqX) yInYYs
    in injective $ permXY anElementInXXs anElementInYYs
  tail permXY occursInOriginal occursInPermutation | (No anElementNEqX) = permXY (There occursInOriginal anElementNEqX) (There occursInPermutation anElementNEqX)
