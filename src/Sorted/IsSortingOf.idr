module Sorted.IsSortingOf

import Control.Function
import Control.Relation
import Control.WellFounded
import Control.Order
import Data.Nat
import Decidable.Equality
import Data.Void

import Sorted.IsPermutationOf
import Sorted.Sorted
import Sorted.Sequence

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
data IsSortingOf: LinearOrder a rel => OutputSequence a c => Rel c where
  Iso: LinearOrder a rel => OutputSequence a c =>
       SizeAccessible @{ContainerSized} sorted =>
       Sorted {a} {c} {rel} sorted =>
       (0 prm: (scrambled ~@~ sorted) {c}) -> IsSortingOf {rel} scrambled sorted

export
infixr 4 -@->

||| If xs is a sorting of ys and ys is a permutation of zs then xs is also a sorting of zs
export
(-@->) : (lo: LinearOrder a rel) => (seq: OutputSequence a c) => IsSortingOf {rel} ys xs -> IsPermutationOf {c} zs ys -> IsSortingOf {rel} {c} zs xs
Iso po -@-> po' = Iso ((po' \=> po) @{transitiveIsPermutationOf})

||| A non-empty container cannot be the sorting of an empty container
export
[uninhabitedIsSortingOfEmptyCons] {0 x:a} -> {0 xs: c} -> LinearOrder a rel => OutputSequence a c => Uninhabited (IsSortingOf {rel} {c} [] (x::xs)) where
  uninhabited (Iso (Ipo isPermutationOfNilXXs)) = void $ SIsNotZ $ (ConsAddsOne \=> (sym $ isPermutationOfNilXXs x)) \=> ∀x‥x⋕【】≐0

export
LinearOrder a rel => OutputSequence a c => Transitive c (IsSortingOf {rel}) where
  transitive (Iso s) (Iso t) = Iso (transitive @{transitiveIsPermutationOf} s t)


export
Nil : LinearOrder a rel => OutputSequence a c => IsSortingOf {rel} {c} (Container.Nil {c}) (Container.Nil {c})
[] = Iso @{_} @{_} @{Access ?huda} @{Sorted.Sorted.Nil} (Ipo (\e => Refl))

-- cons : LinearOrder a rel => Sequence a c => (0 acc: (SizeAccessible @{ContainerSized} orig)) -> (x: a) -> (xs: Subset c (IsSortingOf {c} {rel} orig)) -> Subset c (IsSortingOf {c} {rel} (x::orig))
-- cons acc x (Element f prf) with (Match f)
--   cons acc x (Element f (Iso _ prf)) | (Left fIsNil) = Element [x] (Iso (Singleton x) (x :: replace {p = IsPermutationOf {c} orig} fIsNil prf))
--   cons acc x (Element f prf) | (Right (Element (y, xs) yxsEqF)) with (decEq x y)
--     cons acc x (Element f prf) | (Right (Element (x, xs) yxsEqF)) | (Yes Refl) = Element (x::x::xs) (case (yxsEqF, prf) of (Refl, Iso sXXs pXXs) => Iso ?asda (x :: pXXs)) -- (reflexive :@: sXXs)
--     cons acc x (Element f prf) | (Right (Element (y, xs) yxsEqF)) | (No xNEqY) with (connex {rel} xNEqY)
--       cons acc x (Element f prf) | (Right (Element (y, xs) yxsEqF)) | (No xNEqY) | (Left relXY) = Element (x::y::xs) (case (yxsEqF, prf) of (Refl, Iso sXXs pYXs) => Iso ?basda (x :: pYXs)) -- (relXY :@: sXXs)
--       cons (Access acc) x (Element f (Iso sYXs pYXs)) | (Right (Element (y, xs) yxsEqF)) | (No xNEqY) | (Right relYX) =
--         let
--             Element xs' step = (cons (acc _ $ eqLTE $ sym (PermutationHasSameSize pYXs \=> cong (size @{ContainerSized}) (sym yxsEqF) \=> SizedCons)) x (Element xs (Iso (tail {ysIsCons=Refl} (sYXs)) (reflexive @{reflexiveIsPermutationOf})))) {rel} {orig=xs} 
--         in Element (y::xs') (
--           case (yxsEqF, step) of
--             (Refl, Iso sXs' pXs') =>
--               let
--                 oioi = (replace {p = \q => IsPermutationOf (x::y::xs) q}
--                   (conLeftCons y $ conLeftCons x ConcNilLeftNeutral)
--                   (replace {p = \q => IsPermutationOf q (((y :: ((x :: (Container.Nil {c})) {c})) {c}) ++ xs)}
--                     (conLeftCons x $ conLeftCons y ConcNilLeftNeutral)
--                     (Ipo (swapIsPermutation {x} {y}) ++ reflexive @{reflexiveIsPermutationOf} {x=xs})) \=>
--                       (y :: pXs')) @{transitiveIsPermutationOf}
--                 sol = (((x :: pYXs) \=> oioi) @{transitiveIsPermutationOf} )
--               in Iso (((relYX :: head {ys=f} {ysIsCons=yxsEqF} sYXs) {rel} -@-> pXs') {rel} :: sXs') sol
--         )

-- export
-- (::) : (x: a) -> LinearOrder a rel => Sequence a c => (xs: Subset c (IsSortingOf {c} {rel} orig)) -> Subset c (IsSortingOf {c} {rel} (x::orig))
-- (::) x xs = cons (sizeAccessible @{ContainerSized} orig) x xs

-- public export
-- leanLeft : DecEq a => LinearOrder a rel => (x: a) -> (y: a) -> Either (rel x y) (rel y x)
-- leanLeft x y with (decEq x y)
--   leanLeft x x | (Yes Refl) = Left reflexive
--   leanLeft x y | (No x≠y) = connex x≠y

export
[SizedPairContainers] Container a c => Sized (Pair c c) where
  size (x,y) = size @{ContainerSized} x + size @{ContainerSized} y

covering
isoPlus : DecEq a => LinearOrder a rel => OutputSequence a c => (0 acc: SizeAccessible @{SizedPairContainers} (left, right)) -> Subset c (IsSortingOf {rel} left) -> Subset c (IsSortingOf {rel}  right) -> Subset c (IsSortingOf {rel} (left ++ right))
isoPlus acc (Element sortedLeft isSortingOfLeft) (Element sortedRight isSortingOfRight) = case IsNil sortedLeft of
  Yes Refl => Element sortedRight (
    let
      (Iso isPermutationOfRight) = isSortingOfRight
      (Iso isPermutationOfLeft) = isSortingOfLeft
    in
      Iso (((isPermutationOfLeft ++ (reflexive @{reflexiveIsPermutationOf})) \=> ((ConcNilLeftNeutral \=> isPermutationOfRight) @{transitiveIsPermutationOf})) @{transitiveIsPermutationOf})
    )
  No sortedLeft≠【】 => case IsNil sortedRight of
    Yes Refl => Element sortedLeft (
      let
        (Iso isPermutationOfLeft) = isSortingOfLeft
        (Iso isPermutationOfRight) = isSortingOfRight
      in
        Iso ((((reflexive @{reflexiveIsPermutationOf}) ++ isPermutationOfRight ) \=> ((ConcNilRightNeutral \=> isPermutationOfLeft) @{transitiveIsPermutationOf})) @{transitiveIsPermutationOf})
      )
    No sortedRight≠【】 => -- ?tobecontinued
      case (Match sortedLeft, Match sortedRight) of
        ((Bievidence l ls l∷ls≐sortedLeft), (Bievidence r rs r∷rs≐sortedRight)) => case decEq @{DecEqElement {c}} l r of
          Yes Refl => case isoPlus {a} {rel} (Access ?abula_0) (Element ls (Iso @{_} @{_} @{?hada} @{?nada} (reflexive @{reflexiveIsPermutationOf}))) (Element rs (Iso @{_} @{_} @{?bada} @{?gada} (reflexive @{reflexiveIsPermutationOf}))) of
            Element lsrs srtd =>  Element (l :: r :: lsrs) ?hababa
          No l≠r => case connex {rel} l≠r of
            l≤r => ?huga_1
            r≤l => ?huga_2

-- with (Match sortedLeft, Match sortedRight)
--   isoPlus acc (_ # Iso _ isPermutationOfLeft) (_ # Iso _ isPermutationOfRight) | (Left Refl, Left Refl) = [] # Iso [] (((isPermutationOfLeft ++ isPermutationOfRight) \=> (rewrite ConcNilLeftNeutral {c} {xs=[]} in reflexive @{reflexiveIsPermutationOf})) @{transitiveIsPermutationOf})
--   isoPlus acc (_ # Iso _ isPermutationOfLeft) (sortedRight # Iso isSortedRight isPermutationOfRight) | (Left Refl, Right _) = sortedRight # Iso isSortedRight (((isPermutationOfLeft ++ isPermutationOfRight) \=> (rewrite ConcNilLeftNeutral {xs=sortedRight} in reflexive @{reflexiveIsPermutationOf})) @{transitiveIsPermutationOf})
--   isoPlus acc (sortedLeft # Iso isSortedLeft isPermutationOfLeft) (_ # Iso _ isPermutationOfRight) | (Right _, Left Refl) = sortedLeft # Iso isSortedLeft (((isPermutationOfLeft ++ isPermutationOfRight) \=> (rewrite ConcNilRightNeutral sortedLeft in reflexive @{reflexiveIsPermutationOf})) @{transitiveIsPermutationOf})
--   isoPlus acc (sortedLeft # isSortingOfLeft) (sortedRight # isSortingOfRight) | (Right ((l, ls) # lLsEqSortedLeft), Right ((r, rs) # rRsEqSortedRight)) with (leanLeft {rel} l r)
--     isoPlus (Access acc) (_ # Iso isSortedLeft isPermutationOfLeft) (sortedRight # isSortingOfRight) | (Right ((l, ls) # Refl), Right ((_, _) # _)) | (Left _) =
--       let
--         answer # prf = Sorted.IsSortingOf.(::) l (isoPlus (acc _ $ eqLTE $ sym $ cong (+ size @{ContainerSized} right) (PermutationHasSameSize isPermutationOfLeft \=> SizedCons)) (ls # Iso (tail {ysIsCons=Refl} isSortedLeft) (reflexive @{reflexiveIsPermutationOf})) (sortedRight # isSortingOfRight))
--       in
--         answer #
--           let
--             Iso srtd perm = prf
--           in
--             Iso srtd ((replace {p = IsPermutationOf (left ++ right)} ConcReduces (isPermutationOfLeft ++ reflexive @{reflexiveIsPermutationOf} {x=right}) \=> perm) @{transitiveIsPermutationOf})
--     isoPlus (Access acc) (sortedLeft # isSortingOfLeft) (_ # Iso isSortedRight isPermutationOfRight) | (Right ((_, _) # _), Right ((r, rs) # Refl)) | (Right _) =
--       let
--         answer # prf = Sorted.IsSortingOf.(::) r (isoPlus (acc _ $ eqLTE $ (plusSuccRightSucc _ _ \=> cong (size @{ContainerSized} left +) (sym SizedCons \=> sym (PermutationHasSameSize isPermutationOfRight)))) (sortedLeft # isSortingOfLeft) (rs # Iso (tail {ysIsCons=Refl} isSortedRight) (reflexive @{reflexiveIsPermutationOf})))
--       in
--         answer #
--           let
--             Iso srtd perm = prf
--           in
--             Iso srtd ((shiftPermutation isPermutationOfRight \=> perm) @{transitiveIsPermutationOf})
            
||| Mergig the sorting of left and right produces the sorting of left ++ right
covering
export
(++) : DecEq a => LinearOrder a rel => OutputSequence a c => Subset c (IsSortingOf {rel} left) -> Subset c (IsSortingOf {rel}  right) -> Subset c (IsSortingOf {rel} (left ++ right))
(Element sortedLeft isSortingOfLeft) ++ (Element sortedRight isSortingOfRight) = isoPlus (sizeAccessible @{SizedPairContainers} (left, right)) (Element sortedLeft isSortingOfLeft) (Element sortedRight isSortingOfRight)

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
