module Sorted.MergeSort

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
import public Sorted.IsPermutationOf
import public Sorted.Prop
import public Sorted.Relates
import public Sorted.Sorted
import public Sorted.IsSortingOf

%default total


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

merge' : LinearOrder a rel => {left, right: List a} -> (left': (List a) # (IsSortingOf {rel=rel}  left)) -> (right': (List a) # (IsSortingOf {rel=rel}  right)) -> DecEq a => (List a) # (IsSortingOf {rel=rel} (left ++ right))
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
            (tailSortedLeft  # (tail $ fst isSortingOfLeft, reflexive @{reflexiveIsPermutationOf}))
            ((minRight::tailSortedRight) # (fst isSortingOfRight, reflexive @{reflexiveIsPermutationOf}))
              | acc _ reflexive)
        in (minLeft::merged #
          let
            (mergeIsSorted, Ipo mergeIsPermutationOfSum) = prf
          in case merged of
            [] => let
                (mrInTsr ** mrInTsrPrf) = countOccurrences minRight tailSortedRight
                (mrInTsl ** mrInTslPrf) = countOccurrences minRight tailSortedLeft
                mrInMrTsr = Here mrInTsrPrf
                mrInTotal = mrInTslPrf + mrInMrTsr
                mrw = replace {p = \swee => Occurs minRight swee (tailSortedLeft ++ (minRight::tailSortedRight))} (sym $ plusSuccRightSucc mrInTsl mrInTsr) mrInTotal
              in absurdity $ (mergeIsPermutationOfSum mrw ..=.. Nowhere)
            (mergedH::mergedT) => let
                ml_rel_any_left = head $ fst isSortingOfLeft
                mr_rel_any_right = (reflexive {rel=rel} {x=minRight} :: (head {rel=rel} $ fst isSortingOfRight)) {rel=rel} {x=minRight} 
                ml_rel_any_right: RelatesToAll rel minLeft (minRight::tailSortedRight) = transitive rel_l_r . mr_rel_any_right
                ml_rel_any_lr = (ml_rel_any_left ++ ml_rel_any_right) {rel=rel}
                ml_rel_merged = (ml_rel_any_lr -@-> Ipo mergeIsPermutationOfSum) {rel=rel}
                (mhInMergedT ** mhInMergedTPrf) = countOccurrences mergedH mergedT
                abc = minLeft::(Ipo mergeIsPermutationOfSum)
                cde = snd isSortingOfLeft ++ snd isSortingOfRight
              in (SeveralAreSorted (ml_rel_merged $ Here mhInMergedTPrf) mergeIsSorted, transitive @{transitiveIsPermutationOf} cde abc)
          )
      (Right rel_r_l) =>
        let
          merged # prf = (merge'
            ((minLeft::tailSortedLeft) # (fst isSortingOfLeft, reflexive @{reflexiveIsPermutationOf}))
            (tailSortedRight  # (tail $ fst isSortingOfRight, reflexive @{reflexiveIsPermutationOf}))
              | acc _ (smallerMerge tailSortedLeft minRight tailSortedRight))
        in (minRight::merged #
          let
            (mergeIsSorted, Ipo mergeIsPermutationOfSum) = prf
          in case merged of
            [] => let
                (mlInTsl ** mlInTslPrf) = countOccurrences minLeft tailSortedLeft
                (mlInTsr ** mlInTsrPrf) = countOccurrences minLeft tailSortedRight
                mlInMlTsl = Here mlInTslPrf
                mlInTotal = rewrite sym $ plusSuccRightSucc mlInTsl mlInTsr in mlInMlTsl + mlInTsrPrf
                mrw = replace {p = \swee => Occurs minLeft swee ((minLeft::tailSortedLeft) ++ tailSortedRight)} (sym $ plusSuccRightSucc mlInTsl mlInTsr) mlInTotal
              in absurdity $ (mergeIsPermutationOfSum mrw ..=.. Nowhere)
            (mergedH::mergedT) => let
                mr_rel_any_right = head $ fst isSortingOfRight
                ml_rel_any_left = (reflexive {rel=rel} {x=minLeft} :: (head {rel=rel} $ fst isSortingOfLeft)) {rel=rel} {x=minLeft} 
                mr_rel_any_left: RelatesToAll rel minRight (minLeft::tailSortedLeft) = transitive rel_r_l . ml_rel_any_left
                mr_rel_any_lr = (mr_rel_any_left ++ mr_rel_any_right) {rel=rel}
                mr_rel_merged = (mr_rel_any_lr -@-> Ipo mergeIsPermutationOfSum) {rel=rel}
                (mhInMergedT ** mhInMergedTPrf) = countOccurrences mergedH mergedT
                abc = symmetric @{symmetricIsPermutationOf} $ AdditionOfPermutationsCommutes {xs=minRight::tailSortedRight} (minRight::(AdditionOfPermutationsCommutes {xs=minLeft::tailSortedLeft} $ symmetric @{symmetricIsPermutationOf} $ Ipo mergeIsPermutationOfSum))
                cde = snd isSortingOfLeft ++ snd isSortingOfRight
              in (SeveralAreSorted (mr_rel_merged $ Here mhInMergedTPrf) mergeIsSorted, transitive @{transitiveIsPermutationOf} cde abc)
          )

public export
mergeSort : (as: List a) ->  DecEq a => LinearOrder a rel => (List a) # (IsSortingOf {rel=rel} as)
mergeSort as with (sizeAccessible as)
  mergeSort as | acc with (split as)
    mergeSort [] | acc | SplitNil = [] # (NilIsSorted,  reflexive @{reflexiveIsPermutationOf})
    mergeSort [x] | acc | (SplitOne x) = [x] # (SingletonIsSorted, reflexive @{reflexiveIsPermutationOf})
    mergeSort (x :: (xs ++ (y :: ys))) | Access acc | (SplitPair x xs y ys) with (mergeSort {rel=rel} (x::xs) | acc _ (smallerLeft xs y ys))
      mergeSort (x :: (xs ++ (y :: ys))) | (Access acc) | (SplitPair x xs y ys) | ([] # cantBe ) = absurdity @{uninhabitedIsPermutationOfConsNil} $ snd cantBe
      mergeSort (x :: (xs ++ (y :: ys))) | (Access acc) | (SplitPair x xs y ys) | ((z :: zs) # prfZs) with (mergeSort {rel=rel} (y::ys) | acc _ (smallerRight xs ys))
        mergeSort (x :: (xs ++ (y :: ys))) | (Access rec) | (SplitPair x xs y ys) | ((z :: zs) # prfZs) | ([] # cantBe) = absurdity @{uninhabitedIsPermutationOfConsNil} $ snd cantBe
        mergeSort (x :: (xs ++ (y :: ys))) | (Access rec) | (SplitPair x xs y ys) | ((z :: zs) # prfZs) | ((z' :: zs') # prfZs') = merge' ((z :: zs) # prfZs) ((z' :: zs') # prfZs')
