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
       (0 srt: Sorted {a} {c} {rel} sorted) ->
       (0 prm: (scrambled ~@~ sorted) {c}) -> IsSortingOf {rel} scrambled sorted

0 (.sorted): LinearOrder a rel => OutputSequence a c => IsSortingOf {rel} {c} scr srt -> Sorted {rel} srt
(.sorted) (Iso srtd _) = srtd

0 (.permutation): LinearOrder a rel => OutputSequence a c => IsSortingOf {rel} {c} scr srt -> IsPermutationOf scr srt
(.permutation) (Iso _ perm) = perm

export
infixr 4 -@->

||| If xs is a sorting of ys and ys is a permutation of zs then xs is also a sorting of zs
export
(-@->) : (lo: LinearOrder a rel) => (seq: OutputSequence a c) => IsSortingOf {rel} ys xs -> IsPermutationOf {c} zs ys -> IsSortingOf {rel} {c} zs xs
Iso srt po -@-> po' = Iso srt ((po' \=> po) @{transitiveIsPermutationOf})

||| A non-empty container cannot be the sorting of an empty container
export
[uninhabitedIsSortingOfEmptyCons] {0 x:a} -> {0 xs: c} -> LinearOrder a rel => OutputSequence a c => Uninhabited (IsSortingOf {rel} {c} [] (x::xs)) where
  uninhabited (Iso _ (Ipo isPermutationOfNilXXs)) = void $ SIsNotZ $ (ConsAddsOne \=> (sym $ isPermutationOfNilXXs x)) \=> ∀x‥x⋕【】≐0

export
LinearOrder a rel => OutputSequence a c => Transitive c (IsSortingOf {rel}) where
  transitive (Iso _ s) (Iso st t) = Iso st (transitive @{transitiveIsPermutationOf} s t)


export
Nil : LinearOrder a rel => OutputSequence a c => IsSortingOf {rel} {c} (Container.Nil {c}) (Container.Nil {c})
[] = Iso Sorted.Sorted.Nil (Ipo (\e => Refl))

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

0 smaller : Sequence a c => (permutedLeft≠【】 : Not (permutedLeft = [])) -> (permutedRight≠【】 : Not (permutedRight = [])) -> (isPermutationOfLeft: IsPermutationOf {c} left permutedLeft) -> (isPermutationOfRight: IsPermutationOf {c} right permutedRight) -> LTE (S (plus (size @{ContainerSized {c}} (Tail permutedLeft permutedLeft≠【】)) (size @{ContainerSized {c}} (Tail permutedRight permutedRight≠【】)))) (plus (size @{ContainerSized {c}} left) (size @{ContainerSized {c}} right))
smaller permutedLeft≠【】 permutedRight≠【】 isPermutationOfLeft isPermutationOfRight =
  let
    size_left = sym ((PermutationHasSameSize isPermutationOfLeft) \=> (cong (size @{ContainerSized {c}}) (sym $ HeadTail _ permutedLeft≠【】) \=> ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬))
    size_right = sym ((PermutationHasSameSize isPermutationOfRight) \=> (cong (size @{ContainerSized {c}}) (sym $ HeadTail _ permutedRight≠【】) \=> ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬))
    ala = eqLTE (cong2 (+) size_left size_right)
  in eqLTE (plusSuccRightSucc _ _) \=> lteSuccLeft (eqLTE Refl) \=> eqLTE (cong2 (+) size_left size_right)


succToEq : (n : Nat) -> (p : IsSucc n) -> Subset Nat (\m => n = S m)
succToEq (S _) ItIsSucc = Element _ Refl

notSuccToEq : (n: Nat) -> (p: Not (IsSucc n)) -> n = 0
notSuccToEq 0 p = Refl
notSuccToEq (S _) p = void $ p ItIsSucc

reflexiveFromEq: Reflexive ty rel => {a, b: ty} -> a = b -> rel a b
reflexiveFromEq Refl = reflexive

public export
[SCLeft] DecEq a => Reflexive a rel => Connex a rel => StronglyConnex a rel where
  order x y = case decEq x y of
    (Yes Refl) => Left reflexive
    (No x≠y) => connex x≠y

public export
[SCRight] DecEq a => Reflexive a rel => Connex a rel => StronglyConnex a rel where
  order x y = case decEq x y of
    (Yes Refl) => Right reflexive
    (No x≠y) => connex x≠y

lteBothAddRight: {c: Nat} -> LTE a b -> LTE (a+c) (b+c)
lteBothAddRight {c = 0} x = rewrite cong2 LTE (plusZeroRightNeutral a) (plusZeroRightNeutral b) in x
lteBothAddRight {c = (S k)} x = replace {p = id} (cong2 LTE (plusSuccRightSucc a k) (plusSuccRightSucc b k)) $ LTESucc (lteBothAddRight {c=k} x)


0 isoConc : LinearOrder a rel => Sequence a c => (acc: SizeAccessible @{SizedPairContainers} (left, right)) -> Subset c (IsSortingOf {rel} left) -> Subset c (IsSortingOf {rel}  right) -> Subset c (IsSortingOf {rel} (left ++ right))
isoConc (Access acc) (Element sortedLeft isSortingOfLeft) (Element sortedRight isSortingOfRight) = case IsNil sortedLeft of
  Yes Refl => Element sortedRight (
      Iso isSortingOfRight.sorted (((isSortingOfLeft.permutation ++ (reflexive @{reflexiveIsPermutationOf})) \=> ((ConcNilLeftNeutral \=> isSortingOfRight.permutation) @{transitiveIsPermutationOf})) @{transitiveIsPermutationOf})
    )
  No sortedLeft≠【】 => case IsNil sortedRight of
    Yes Refl => Element sortedLeft (
        Iso isSortingOfLeft.sorted ((((reflexive @{reflexiveIsPermutationOf}) ++ isSortingOfRight.permutation ) \=> ((ConcNilRightNeutral \=> isSortingOfLeft.permutation) @{transitiveIsPermutationOf})) @{transitiveIsPermutationOf})
      )
    No sortedRight≠【】 =>
        case order @{SCLeft {rel}} (Head sortedLeft sortedLeft≠【】) (Head sortedRight sortedRight≠【】) of
          Left l≤r => case isoConc {a} {rel} (acc _ (lteBothAddRight {c=size @{ContainerSized {c}} right} $ eqLTE (TailIsShorter sortedLeft sortedLeft≠【】 \=> (sym $ PermutationHasSameSize isSortingOfLeft.permutation)))) (Element (Tail sortedLeft sortedLeft≠【】) (Iso (tail isSortingOfLeft.sorted) (reflexive @{reflexiveIsPermutationOf}))) (Element sortedRight isSortingOfRight) of
             Element step srtd =>
              Element (Head sortedLeft sortedLeft≠【】 :: step) $
                Iso
                  (((((Relates.(++) {c} {rel} (head sortedLeft sortedLeft≠【】 isSortingOfLeft.sorted) $ (RelatesToAllTheRest sortedRight≠【】 l≤r isSortingOfRight.sorted -@-> (symmetric @{symmetricIsPermutationOf} isSortingOfRight.permutation)) {rel}) -@-> srtd.permutation) {rel} {x=Head sortedLeft sortedLeft≠【】}) :: srtd.sorted))
                  ((((((isSortingOfLeft.permutation \=> (reflexiveFromEq @{reflexiveIsPermutationOf} $ sym $ HeadTail sortedLeft sortedLeft≠【】)) @{transitiveIsPermutationOf}) ++ reflexive @{reflexiveIsPermutationOf}) \=> x∷xs⧺ys≐x∷⎨xs⧺ys⎬) @{transitiveIsPermutationOf} \=> _ :: srtd.permutation) @{transitiveIsPermutationOf})
          Right r≤l => case isoConc {a} {rel} (acc _ ((lteBothAddRight {a=S (size @{ContainerSized {c}} (Tail sortedRight sortedRight≠【】))} {b=size @{ContainerSized {c}} right} {c=size @{ContainerSized {c}} left} (eqLTE (TailIsShorter sortedRight sortedRight≠【】 \=> (sym $ PermutationHasSameSize isSortingOfRight.permutation))) \=> eqLTE (plusCommutative _ _)))) (Element (Tail sortedRight sortedRight≠【】) (Iso (tail isSortingOfRight.sorted) (reflexive @{reflexiveIsPermutationOf}))) (Element sortedLeft isSortingOfLeft) of
             Element step srtd =>
              Element (Head sortedRight sortedRight≠【】 :: step) $
                Iso
                  (((((Relates.(++) {c} {rel} (head sortedRight sortedRight≠【】 isSortingOfRight.sorted) $ (RelatesToAllTheRest sortedLeft≠【】 r≤l isSortingOfLeft.sorted -@-> (symmetric @{symmetricIsPermutationOf} isSortingOfLeft.permutation)) {rel}) -@-> srtd.permutation) {rel} {x=Head sortedRight sortedRight≠【】}) :: srtd.sorted))
                  ((AdditionOfPermutationsCommutes (reflexive @{reflexiveIsPermutationOf}) \=> ((((((isSortingOfRight.permutation \=> (reflexiveFromEq @{reflexiveIsPermutationOf} $ sym $ HeadTail sortedRight sortedRight≠【】)) @{transitiveIsPermutationOf}) ++ reflexive @{reflexiveIsPermutationOf}) \=> x∷xs⧺ys≐x∷⎨xs⧺ys⎬) @{transitiveIsPermutationOf} \=> _ :: srtd.permutation) @{transitiveIsPermutationOf})) @{transitiveIsPermutationOf})


||| Mergig the sorting of left and right produces the sorting of left ++ right
||| This algorithm is known as "SortedMerge" and is an important component of MergeSort
covering
export
0 (++) : DecEq a => LinearOrder a rel => Sequence a c => Subset c (IsSortingOf {rel} left) -> Subset c (IsSortingOf {rel}  right) -> Subset c (IsSortingOf {rel} (left ++ right))
(++) xs ys = isoConc (sizeAccessible @{SizedPairContainers} (left, right)) xs ys

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
