module Sorted.IsSortingOf

import Control.Function
import Control.Relation
import Control.WellFounded
import Control.Order
import Data.Nat
import Decidable.Equality

import Sorted.Container
import Sorted.IsPermutationOf
import Sorted.Prop
import Sorted.Relates
import public Sorted.Sorted

%default total

%hide Prelude.Types.List.(++)
%hide Prelude.Types.SnocList.(++)
%hide Prelude.Types.String.(++)
%hide Prelude.(::)
%hide Prelude.Nil
%hide Stream.(::)

||| sorted is a sorting of scrambled according to the ordering induced by rel if
||| sorted is both sorted and it is a permutation of scrambled.
public export
data IsSortingOf : LinearOrder a rel => Container a c => Rel c where
    Iso: (Sorted @{lo} @{ct} sorted) -> (scrambled ~@~ sorted) @{ct} -> IsSortingOf @{lo} @{ct} scrambled sorted

infixr 4 -@->

export
0 (-@->) : LinearOrder a rel => Container a c => IsSortingOf {rel} {c} ys xs -> IsPermutationOf zs ys -> IsSortingOf {rel} zs xs
Iso std po -@-> po' = Iso std ((po' \=> po) @{transitiveIsPermutationOf})

export
[uninhabitedIsSortingOfEmptyCons] {0 x:a} -> {0 xs: c} -> LinearOrder a rel => Container a c => Uninhabited (IsSortingOf {rel} {c} [] (x::xs)) where
    uninhabited (Iso sortedXXs (Ipo isPermutationOfNilXXs)) = void $ SIsNotZ $ (ConsAddsOne \=> (sym $ isPermutationOfNilXXs x)) \=> NilIsEmpty

export
DecEq a => LinearOrder a rel => Container a c => Transitive c (IsSortingOf {rel}) where
    transitive (Iso _ s) (Iso w t) = Iso w (transitive @{transitiveIsPermutationOf} s t)


export
Nil : LinearOrder a rel => Container a c => IsSortingOf {rel} {c} (Container.Nil {c}) (Container.Nil {c})
[] = Iso [] (Ipo (\e => Refl))

cons : LinearOrder a rel => Container a c => (0 acc: (SizeAccessible @{ContainerSized} orig)) -> (x: a) -> (xs: c # (IsSortingOf {c} {rel} orig)) -> DecEq a => c # (IsSortingOf {c} {rel} (x::orig))
cons acc x (f # prf) with (Match f)
  cons acc x (f # (Iso _ prf)) | (Left fIsNil) = [x] # Iso (Singleton x) (x :: replace {p = IsPermutationOf {c} orig} fIsNil prf)
  cons acc x (f # prf) | (Right ((y, xs) # yxsEqF)) with (decEq x y)
    cons acc x (f # prf) | (Right ((x, xs) # yxsEqF)) | (Yes Refl) = (x::x::xs) # case (yxsEqF, prf) of (Refl, Iso sXXs pXXs) => Iso (reflexive :@: sXXs) (x :: pXXs)
    cons acc x (f # prf) | (Right ((y, xs) # yxsEqF)) | (No xNEqY) with (connex {rel} xNEqY)
      cons acc x (f # prf) | (Right ((y, xs) # yxsEqF)) | (No xNEqY) | (Left relXY) = (x::y::xs) # case (yxsEqF, prf) of (Refl, Iso sXXs pYXs) => Iso (relXY :@: sXXs) (x :: pYXs)
      cons (Access acc) x (f # Iso sYXs pYXs) | (Right ((y, xs) # yxsEqF)) | (No xNEqY) | (Right relYX) =
        let
            xs' # step = (cons (acc _ $ eqLTE $ sym (PermutationHasSameSize pYXs \=> cong (size @{ContainerSized}) (sym yxsEqF) \=> SizedCons)) x (xs # Iso (tail {ysIsCons=yxsEqF} (sYXs)) (reflexive @{reflexiveIsPermutationOf}))) {rel} {orig=xs} 
        in (y::xs') #
          case (yxsEqF, step) of
            (Refl, Iso sXs' pXs') =>
              let
                oioi = (replace {p = \q => IsPermutationOf (x::y::xs) q}
                  (conLeftCons y $ conLeftCons x ConcNilLeftNeutral)
                  (replace {p = \q => IsPermutationOf q (((y :: ((x :: (Container.Nil {c})) {c})) {c}) ++ xs)}
                    (conLeftCons x $ conLeftCons y ConcNilLeftNeutral)
                    (Ipo (swapIsPermutation {x} {y}) ++ reflexive @{reflexiveIsPermutationOf} {x=xs})) \=>
                      (y :: pXs')) @{transitiveIsPermutationOf}
                sol = (((x :: pYXs) \=> oioi) @{transitiveIsPermutationOf} )
              in Iso (((relYX :: head {ys=f} {ysIsCons=yxsEqF} sYXs) {rel} -@-> pXs') {rel} :: sXs') sol

export
(::) : (x: a) -> LinearOrder a rel => Container a c => (xs: Prop c (IsSortingOf {c} {rel} orig)) -> DecEq a => c # (IsSortingOf {c} {rel} (x::orig))
(::) x xs = cons (sizeAccessible @{ContainerSized} orig) x xs

leanLeft : DecEq a => LinearOrder a rel => (x: a) -> (y: a) -> Either (rel x y) (rel y x)
leanLeft x y with (decEq x y)
  leanLeft x x | (Yes Refl) = Left reflexive
  leanLeft x y | (No xNEqY) = connex xNEqY

export
[SizedPairContainers] Container a c => Sized (Pair c c) where
  size (x,y) = size @{ContainerSized} x + size @{ContainerSized} y

isoPlus : DecEq a => LinearOrder a rel => Container a c => (0 acc: SizeAccessible @{SizedPairContainers} (left, right)) -> c # (IsSortingOf {rel} left) -> c # (IsSortingOf {rel}  right) -> c # (IsSortingOf {rel} (left ++ right))
isoPlus acc (sortedLeft # isSortingOfLeft) (sortedRight # isSortingOfRight) with (Match sortedLeft, Match sortedRight)
  isoPlus acc (_ # Iso _ isPermutationOfLeft) (_ # Iso _ isPermutationOfRight) | (Left Refl, Left Refl) = [] # Iso [] (((isPermutationOfLeft ++ isPermutationOfRight) \=> (rewrite ConcNilLeftNeutral {c} {xs=[]} in reflexive @{reflexiveIsPermutationOf})) @{transitiveIsPermutationOf})
  isoPlus acc (_ # Iso _ isPermutationOfLeft) (sortedRight # Iso isSortedRight isPermutationOfRight) | (Left Refl, Right _) = sortedRight # Iso isSortedRight (((isPermutationOfLeft ++ isPermutationOfRight) \=> (rewrite ConcNilLeftNeutral {xs=sortedRight} in reflexive @{reflexiveIsPermutationOf})) @{transitiveIsPermutationOf})
  isoPlus acc (sortedLeft # Iso isSortedLeft isPermutationOfLeft) (_ # Iso _ isPermutationOfRight) | (Right _, Left Refl) = sortedLeft # Iso isSortedLeft (((isPermutationOfLeft ++ isPermutationOfRight) \=> (rewrite ConcNilRightNeutral sortedLeft in reflexive @{reflexiveIsPermutationOf})) @{transitiveIsPermutationOf})
  isoPlus acc (sortedLeft # isSortingOfLeft) (sortedRight # isSortingOfRight) | (Right ((l, ls) # lLsEqSortedLeft), Right ((r, rs) # rRsEqSortedRight)) with (leanLeft {rel} l r)
    isoPlus (Access acc) (_ # Iso isSortedLeft isPermutationOfLeft) (sortedRight # isSortingOfRight) | (Right ((l, ls) # Refl), Right ((_, _) # _)) | (Left _) =
      let
        answer # prf = Sorted.IsSortingOf.(::) l (isoPlus (acc _ $ eqLTE $ sym $ cong (+ size @{ContainerSized} right) (PermutationHasSameSize isPermutationOfLeft \=> SizedCons)) (ls # Iso (tail {ysIsCons=Refl} isSortedLeft) (reflexive @{reflexiveIsPermutationOf})) (sortedRight # isSortingOfRight))
      in
        answer #
          let
            Iso srtd perm = prf
          in
            Iso srtd ((replace {p = IsPermutationOf (left ++ right)} ConcReduces (isPermutationOfLeft ++ reflexive @{reflexiveIsPermutationOf} {x=right}) \=> perm) @{transitiveIsPermutationOf})
    isoPlus (Access acc) (sortedLeft # isSortingOfLeft) (_ # Iso isSortedRight isPermutationOfRight) | (Right ((_, _) # _), Right ((r, rs) # Refl)) | (Right _) =
      let
        answer # prf = Sorted.IsSortingOf.(::) r (isoPlus (acc _ $ eqLTE $ (plusSuccRightSucc _ _ \=> cong (size @{ContainerSized} left +) (sym SizedCons \=> sym (PermutationHasSameSize isPermutationOfRight)))) (sortedLeft # isSortingOfLeft) (rs # Iso (tail {ysIsCons=Refl} isSortedRight) (reflexive @{reflexiveIsPermutationOf})))
      in
        answer #
          let
            Iso srtd perm = prf
          in
            Iso srtd ((shiftPermutation isPermutationOfRight \=> perm) @{transitiveIsPermutationOf})
            
||| Mergig the sorting of left and right produces the sorting of left ++ right
export
(++) : DecEq a => LinearOrder a rel => Container a c => c # (IsSortingOf {rel} left) -> c # (IsSortingOf {rel}  right) -> c # (IsSortingOf {rel} (left ++ right))
(sortedLeft # isSortingOfLeft) ++ (sortedRight # isSortingOfRight) = isoPlus (sizeAccessible @{SizedPairContainers} (left, right)) (sortedLeft # isSortingOfLeft) (sortedRight # isSortingOfRight)

-- aiso : DecEq a => (xs: List a) -> (ys: List a) -> (lo: LinearOrder a rel) => (isoXY: IsSortingOf lo xs ys) -> (isoYX : IsSortingOf lo ys xs) -> xs = ys
-- aiso [] [] isoXY isoYX = Refl
-- aiso [] (x :: xs) isoXY isoYX = absurdity @{uninhabitedIsPermutationOfNilCons} $ snd isoXY
-- aiso (x :: xs) [] isoXY isoYX = absurdity @{uninhabitedIsPermutationOfNilCons} $ snd isoYX
-- aiso (x::xs) (y::ys) (sortedY, ipoXY) (sortedX, ipoYX) with (decEq x y)
--   aiso (x::xs) (y::ys) (sortedY, ipoXY) (sortedX, ipoYX) | (No xNEqY) =
--     let
--       xRelYs = ((reflexive :: head sortedX) {rel=rel} -@-> ipoXY) {rel=rel}
--       yRelXs = ((reflexive :: head sortedY) {rel=rel} -@-> ipoYX) {rel=rel}
--       (xInXs ** xInXsPrf) = countOccurrences x xs
--       (yInYs ** yInYsPrf) = countOccurrences y ys
--       relXY = xRelYs (Here yInYsPrf)
--       relYX = yRelXs (Here xInXsPrf)
--     in void $ xNEqY $ antisymmetric relXY relYX
--   aiso (x::xs) (y::ys) (sortedY, ipoXY) (sortedX, ipoYX) | (Yes xEqY) =
--     let
--       ipoXY' = replace {p = \q => q::xs ~@~ y::ys } xEqY ipoXY
--       ipoYX' = replace {p = \q => q::ys ~@~ x::xs } (sym xEqY) ipoYX
--       step = aiso xs ys (tail sortedY, tail ipoXY') (tail sortedX, tail ipoYX')
--     in cong2 (::) xEqY step

-- export
-- [antisymmetricIsSortingOf] DecEq a => (lo: LinearOrder a rel) => Antisymmetric (List a) (IsSortingOf lo) where
--     antisymmetric isoXY isoYX = aiso x y isoXY isoYX
