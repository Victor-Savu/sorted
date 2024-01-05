module Sorted.List

import Control.Order
import Control.Relation
import Control.WellFounded
import Data.Linear.Notation
import Data.Nat
import Data.Nat.Views
import Data.List
import Data.List.Views
import Data.List.Quantifiers
import Data.Void
import Decidable.Equality

import public Sorted.Occurs
import public Sorted.Perm
import public Sorted.Prop
import public Sorted.Relates

%default total

-- Sorted

public export
data Sorted: LinearOrder a rel => List a -> Type where
    NilIsSorted: (0 lo: LinearOrder a rel) => Sorted @{lo} Nil
    SingletonIsSorted : (0 lo: LinearOrder a rel) => Sorted @{lo} [x]
    SeveralAreSorted: {x, y: a} -> rel x y -> (0 lo: LinearOrder a rel) => Sorted @{lo} (y::ys) -> Sorted @{lo} (x::y::ys)

public export
sortedTail : (0 lo: LinearOrder a rel) => Sorted @{lo} (x::xs) -> Sorted @{lo} xs
sortedTail SingletonIsSorted = NilIsSorted
sortedTail (SeveralAreSorted z w) = w

public export
sortedHead : (lo: LinearOrder a rel) => Sorted @{lo} (x::xs) -> RelatesToAll rel x xs
sortedHead SingletonIsSorted z = absurdity @{uninhabitedOccursAtLeastOnceInNil} z
sortedHead (SeveralAreSorted y _) (Here _) = y
sortedHead (SeveralAreSorted y w) (There z f) = transitive y $ sortedHead w z

-- \Sorted

public export
0 IsSortingOf : (lo: LinearOrder a rel) => Rel (List a)
IsSortingOf as = Sorted @{lo} && (as ~@~)

public export
[uninhabitedIsSortingOfEmptyCons] {0 a: Type} -> {0 rel: Rel a} -> {0 x:a} -> {0 xs: List a} -> DecEq a => (lo: LinearOrder a rel) => Uninhabited (IsSortingOf @{lo} [] (x::xs)) where
    uninhabited (_, isPermutationOfNilXXs) = absurdity @{uninhabitedIsPermutationOfNilCons} isPermutationOfNilXXs

public export
{0 a: Type} -> {0 rel: Rel a} -> DecEq a => (lo: LinearOrder a rel) => Transitive (List a) (IsSortingOf @{lo}) where
    transitive (_, s) (w, t) = (w, transitive @{transitiveIsPermutationOf} s t)

ElemOfPermutation : {e: a} -> {n: Nat} -> {xs, ys: List a} -> DecEq a => xs ~@~ ys -> Occurs e (S n) xs -> Occurs e (S n) ys
ElemOfPermutation {n} {xs} {ys} isPermutationOfXsYs eInXs with (countOccurrences e ys)
  ElemOfPermutation {xs = xs} {ys = ys} isPermutationOfXsYs eInXs | (0 ** snd) with (isPermutationOfXsYs eInXs snd)
    ElemOfPermutation {xs = xs} {ys = ys} isPermutationOfXsYs eInXs | (0 ** snd) | _ impossible
  ElemOfPermutation {n} {xs = xs} {ys = ys} isPermutationOfXsYs eInXs | ((S k) ** snd) with (isPermutationOfXsYs eInXs snd)
    ElemOfPermutation {n} {xs = xs} {ys = ys} isPermutationOfXsYs eInXs | ((S n) ** snd) | Refl = snd


aiso : (de: DecEq a) => (lo: LinearOrder a rel) => (xs: List a) -> (ys: List a) -> (isoXY: IsSortingOf @{lo} xs ys) -> (isoYX : IsSortingOf @{lo} ys xs) -> xs = ys
aiso [] [] isoXY isoYX = Refl
aiso [] (x :: xs) isoXY isoYX = absurdity @{uninhabitedIsPermutationOfNilCons} $ snd isoXY
aiso (x :: xs) [] isoXY isoYX = absurdity @{uninhabitedIsPermutationOfNilCons} $ snd isoYX
aiso (x::xs) (y::ys) (sortedY, ipoXY) (sortedX, ipoYX) with (decEq x y)
  aiso (x::xs) (y::ys) (sortedY, ipoXY) (sortedX, ipoYX) | (No xNEqY) =
    let
      xRelYs = ((reflexive :: sortedHead sortedX) {rel=rel} -@-> ipoXY) {rel=rel}
      yRelXs = ((reflexive :: sortedHead sortedY) {rel=rel} -@-> ipoYX) {rel=rel}
      (xInXs ** xInXsPrf) = countOccurrences x xs
      (yInYs ** yInYsPrf) = countOccurrences y ys
      relXY = xRelYs (y :: yInYsPrf)
      relYX = yRelXs (x :: xInXsPrf)
    in void $ xNEqY $ antisymmetric relXY relYX
  aiso (x::xs) (y::ys) (sortedY, ipoXY) (sortedX, ipoYX) | (Yes xEqY) =
    let
      ipoXY' = replace {p = \q => q::xs ~@~ y::ys } xEqY ipoXY
      ipoYX' = replace {p = \q => q::ys ~@~ x::xs } (sym xEqY) ipoYX
      step = aiso xs ys (sortedTail sortedY, tail ipoXY') (sortedTail sortedX, tail ipoYX')
    in cong2 (::) xEqY step

public export
[antisymmetricIsSortingOf] (de: DecEq a) => (lo: LinearOrder a rel) => Antisymmetric (List a) (IsSortingOf @{lo}) where
    antisymmetric isoXY isoYX = aiso x y isoXY isoYX

lengthSuc : (xs : List a) -> (y : a) -> (ys : List a) ->
            length (xs ++ (y :: ys)) = S (length (xs ++ ys))
lengthSuc [] _ _ = Refl
lengthSuc (x :: xs) y ys = cong S (lengthSuc xs y ys)

lengthLT : (xs : List a) -> (ys : List a) ->
           LTE (length xs) (length (ys ++ xs))
lengthLT xs [] = reflexive {x = length xs}
lengthLT xs (x :: ys) = lteSuccRight (lengthLT _ _)

smallerLeft : (ys : List a) -> (y : a) -> (zs : List a) ->
              LTE (S (S (length ys))) (S (length (ys ++ (y :: zs))))
smallerLeft [] y zs = LTESucc (LTESucc LTEZero)
smallerLeft (z :: ys) y zs = LTESucc (smallerLeft ys _ _)

smallerRight : (ys : List a) -> (zs : List a) ->
               LTE (S (S (length zs))) (S (length (ys ++ (y :: zs))))
smallerRight ys zs = rewrite lengthSuc ys y zs in
                     (LTESucc (LTESucc (lengthLT _ _)))

smallerMerge : (xs: List a) -> (y: a) -> (ys: List a) ->  LTE (S (S (length (xs ++ ys)))) (S (length (xs ++ (y :: ys))))
smallerMerge xs y ys = LTESucc $ replace {p = \arg => LTE arg (length (xs ++ (y::ys))) } (lengthSuc xs y ys) (reflexive {x=length (xs++(y::ys))})

-- The sorting of a list starts with the minimum element. The If we have a sorting 

merge' : (lo: LinearOrder a rel) => {left, right: List a} -> (left': (List a) # (IsSortingOf @{lo}  left)) -> (right': (List a) # (IsSortingOf @{lo}  right)) -> DecEq a => (List a) # (IsSortingOf @{lo} (left ++ right))
merge' (sortedLeft # isSortingOfLeft) (sortedRight # isSortingOfRight) with (sizeAccessible (sortedLeft ++ sortedRight))
  merge' {left = []} {right = right} ((w :: xs1) # isSortingOfLeft) (sortedRight # isSortingOfRight) | acc = absurdity @{uninhabitedIsPermutationOfNilCons} $ snd isSortingOfLeft
  merge' {left = []} {right = right} ([] # isSortingOfLeft) (sortedRight # isSortingOfRight) | acc = (sortedRight # isSortingOfRight)
  merge' {left = (w :: xs1)} {right = []} (sortedLeft # isSortingOfLeft) (sortedRight # isSortingOfRight) | acc = rewrite sameasitis {xs=(w::xs1)} in (sortedLeft # isSortingOfLeft)
  merge' {left = (w :: xs1)} {right = (v :: ys1)} ([] # isSortingOfLeft) (sortedRight # isSortingOfRight) | acc = absurdity @{uninhabitedIsPermutationOfConsNil} $ snd isSortingOfLeft
  merge' {left = (w :: xs1)} {right = (v :: ys1)} ((minLeft :: tailSortedLeft) # isSortingOfLeft) ([] # isSortingOfRight) | acc = absurdity @{uninhabitedIsPermutationOfConsNil} $ snd isSortingOfRight
  merge' {left = (w :: xs1)} {right = (v :: ys1)} ((minLeft :: tailSortedLeft) # isSortingOfLeft) ((minRight::tailSortedRight) # isSortingOfRight) | Access acc =
    let
      disc : Either (rel minLeft minRight) (rel minRight minLeft) = case (decEq minLeft minRight) of
        (Yes mlEqMr) => Right $ rewrite mlEqMr in reflexive
        (No contra) => connex contra
    in case disc of
      (Left rel_l_r) =>
        let
          merged # prf = (merge'
            (tailSortedLeft  # (sortedTail $ fst isSortingOfLeft, reflexive @{reflexiveIsPermutationOf}))
            ((minRight::tailSortedRight) # (fst isSortingOfRight, reflexive @{reflexiveIsPermutationOf}))
              | acc _ reflexive)
        in (minLeft::merged #
          let
            (mergeIsSorted, mergeIsPermutationOfSum) = prf
          in case merged of
            [] => let
                (mrInTsr ** mrInTsrPrf) = countOccurrences minRight tailSortedRight
                (mrInTsl ** mrInTslPrf) = countOccurrences minRight tailSortedLeft
                mrInMrTsr = Here mrInTsrPrf
                mrInTotal = mrInTslPrf + mrInMrTsr
                mrw = replace {p = \swee => Occurs minRight swee (tailSortedLeft ++ (minRight::tailSortedRight))} (sym $ plusSuccRightSucc mrInTsl mrInTsr) mrInTotal
              in absurdity $ mergeIsPermutationOfSum mrw Nowhere
            (mergedH::mergedT) => let
                ml_rel_any_left = sortedHead $ fst isSortingOfLeft
                mr_rel_any_right = (reflexive {rel=rel} {x=minRight} :: (sortedHead {rel=rel} $ fst isSortingOfRight)) {rel=rel} {x=minRight} 
                ml_rel_any_right: RelatesToAll rel minLeft (minRight::tailSortedRight) = transitive rel_l_r . mr_rel_any_right
                ml_rel_any_lr = (ml_rel_any_left ++ ml_rel_any_right) {rel=rel}
                ml_rel_merged = (ml_rel_any_lr -@-> mergeIsPermutationOfSum) {rel=rel}
                (mhInMergedT ** mhInMergedTPrf) = countOccurrences mergedH mergedT
                abc = minLeft::mergeIsPermutationOfSum
                cde = snd isSortingOfLeft ++ snd isSortingOfRight
              in (SeveralAreSorted (ml_rel_merged $ Here mhInMergedTPrf) mergeIsSorted, transitive @{transitiveIsPermutationOf} cde abc)
          )
      (Right rel_r_l) =>
        let
          merged # prf = (merge'
            ((minLeft::tailSortedLeft) # (fst isSortingOfLeft, reflexive @{reflexiveIsPermutationOf}))
            (tailSortedRight  # (sortedTail $ fst isSortingOfRight, reflexive @{reflexiveIsPermutationOf}))
              | acc _ (smallerMerge tailSortedLeft minRight tailSortedRight))
        in (minRight::merged #
          let
            (mergeIsSorted, mergeIsPermutationOfSum) = prf
          in case merged of
            [] => let
                (mlInTsl ** mlInTslPrf) = countOccurrences minLeft tailSortedLeft
                (mlInTsr ** mlInTsrPrf) = countOccurrences minLeft tailSortedRight
                mlInMlTsl = Here mlInTslPrf
                mlInTotal = rewrite sym $ plusSuccRightSucc mlInTsl mlInTsr in mlInMlTsl + mlInTsrPrf
                mrw = replace {p = \swee => Occurs minLeft swee ((minLeft::tailSortedLeft) ++ tailSortedRight)} (sym $ plusSuccRightSucc mlInTsl mlInTsr) mlInTotal
              in absurdity $ mergeIsPermutationOfSum mrw Nowhere
            (mergedH::mergedT) => let
                mr_rel_any_right = sortedHead $ fst isSortingOfRight
                ml_rel_any_left = (reflexive {rel=rel} {x=minLeft} :: (sortedHead {rel=rel} $ fst isSortingOfLeft)) {rel=rel} {x=minLeft} 
                mr_rel_any_left: RelatesToAll rel minRight (minLeft::tailSortedLeft) = transitive rel_r_l . ml_rel_any_left
                mr_rel_any_lr = (mr_rel_any_left ++ mr_rel_any_right) {rel=rel}
                mr_rel_merged = (mr_rel_any_lr -@-> mergeIsPermutationOfSum) {rel=rel}
                (mhInMergedT ** mhInMergedTPrf) = countOccurrences mergedH mergedT
                abc = symmetric @{symmetricIsPermutationOf} $ AdditionOfPermutationsCommutes {xs=minRight::tailSortedRight} (minRight::(AdditionOfPermutationsCommutes {xs=minLeft::tailSortedLeft} $ symmetric @{symmetricIsPermutationOf} mergeIsPermutationOfSum))
                cde = snd isSortingOfLeft ++ snd isSortingOfRight
              in (SeveralAreSorted (mr_rel_merged $ Here mhInMergedTPrf) mergeIsSorted, transitive @{transitiveIsPermutationOf} cde abc)
          )

public export
mergeSort :(as: List a) ->  DecEq a => (lo: LinearOrder a rel) => (List a) # (IsSortingOf @{lo} as)
mergeSort as with (sizeAccessible as)
  mergeSort as | acc with (split as)
    mergeSort [] | acc | SplitNil = [] # (NilIsSorted,  reflexive @{reflexiveIsPermutationOf})
    mergeSort [x] | acc | (SplitOne x) = [x] # (SingletonIsSorted, reflexive @{reflexiveIsPermutationOf})
    mergeSort (x :: (xs ++ (y :: ys))) | Access acc | (SplitPair x xs y ys) with (mergeSort (x::xs) | acc _ (smallerLeft xs y ys))
      mergeSort (x :: (xs ++ (y :: ys))) | (Access acc) | (SplitPair x xs y ys) | ([] # cantBe ) = absurdity @{uninhabitedIsPermutationOfConsNil} $ snd cantBe
      mergeSort (x :: (xs ++ (y :: ys))) | (Access acc) | (SplitPair x xs y ys) | ((z :: zs) # prfZs) with (mergeSort (y::ys) | acc _ (smallerRight xs ys))
        mergeSort (x :: (xs ++ (y :: ys))) | (Access rec) | (SplitPair x xs y ys) | ((z :: zs) # prfZs) | ([] # cantBe) = absurdity @{uninhabitedIsPermutationOfConsNil} $ snd cantBe
        mergeSort (x :: (xs ++ (y :: ys))) | (Access rec) | (SplitPair x xs y ys) | ((z :: zs) # prfZs) | ((z' :: zs') # prfZs') = merge' ((z :: zs) # prfZs) ((z' :: zs') # prfZs')
