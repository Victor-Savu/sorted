module Sorted.IsSortingOf

import Control.Relation

import Sorted.Occurs
import Sorted.Perm
import Sorted.Prop
import Sorted.Relates
import Sorted.Sorted

%default total


public export
0 IsSortingOf : (lo: LinearOrder a rel) => Rel (List a)
IsSortingOf as = Sorted @{lo} && (as ~@~)

public export
[uninhabitedIsSortingOfEmptyCons] {0 a: Type} -> {0 rel: Rel a} -> {0 x:a} -> {0 xs: List a} -> DecEq a => (lo: LinearOrder a rel) => Uninhabited (IsSortingOf @{lo} [] (x::xs)) where
    uninhabited (_, isPermutationOfNilXXs) = absurdity @{uninhabitedIsPermutationOfNilCons} isPermutationOfNilXXs

public export
{0 a: Type} -> {0 rel: Rel a} -> DecEq a => (lo: LinearOrder a rel) => Transitive (List a) (IsSortingOf @{lo}) where
    transitive (_, s) (w, t) = (w, transitive @{transitiveIsPermutationOf} s t)

aiso : (de: DecEq a) => (lo: LinearOrder a rel) => (xs: List a) -> (ys: List a) -> (isoXY: IsSortingOf @{lo} xs ys) -> (isoYX : IsSortingOf @{lo} ys xs) -> xs = ys
aiso [] [] isoXY isoYX = Refl
aiso [] (x :: xs) isoXY isoYX = absurdity @{uninhabitedIsPermutationOfNilCons} $ snd isoXY
aiso (x :: xs) [] isoXY isoYX = absurdity @{uninhabitedIsPermutationOfNilCons} $ snd isoYX
aiso (x::xs) (y::ys) (sortedY, ipoXY) (sortedX, ipoYX) with (decEq x y)
  aiso (x::xs) (y::ys) (sortedY, ipoXY) (sortedX, ipoYX) | (No xNEqY) =
    let
      xRelYs = ((reflexive :: head sortedX) {rel=rel} -@-> ipoXY) {rel=rel}
      yRelXs = ((reflexive :: head sortedY) {rel=rel} -@-> ipoYX) {rel=rel}
      (xInXs ** xInXsPrf) = countOccurrences x xs
      (yInYs ** yInYsPrf) = countOccurrences y ys
      relXY = xRelYs (y :: yInYsPrf)
      relYX = yRelXs (x :: xInXsPrf)
    in void $ xNEqY $ antisymmetric relXY relYX
  aiso (x::xs) (y::ys) (sortedY, ipoXY) (sortedX, ipoYX) | (Yes xEqY) =
    let
      ipoXY' = replace {p = \q => q::xs ~@~ y::ys } xEqY ipoXY
      ipoYX' = replace {p = \q => q::ys ~@~ x::xs } (sym xEqY) ipoYX
      step = aiso xs ys (tail sortedY, tail ipoXY') (tail sortedX, tail ipoYX')
    in cong2 (::) xEqY step

public export
[antisymmetricIsSortingOf] (de: DecEq a) => (lo: LinearOrder a rel) => Antisymmetric (List a) (IsSortingOf @{lo}) where
    antisymmetric isoXY isoYX = aiso x y isoXY isoYX
