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

import public Sorted.Container
import public Sorted.IsPermutationOf
import public Sorted.Prop
import public Sorted.Relates
import public Sorted.Sorted
import public Sorted.IsSortingOf

%default total

-- Helper functions for proving termination

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

infixl 4 \=>

(\=>) : {x, y, z: ty} -> Transitive ty rel => rel x y -> rel y z -> rel x z
a \=> b = transitive a b

||| Mergig the sorting of left and right produces the sorting of left ++ right
merge' : DecEq a => LinearOrder a rel => {left, right: List a} -> (left': (List a) # (IsSortingOf {rel} left)) -> (right': (List a) # (IsSortingOf {rel} right)) -> (List a) # (IsSortingOf {rel} (left ++ right))
merge' (sortedLeft # isSortingOfLeft) (sortedRight # isSortingOfRight) with (sizeAccessible (Prelude.List.(++) sortedLeft sortedRight))
  merge' {left = []} {right = right} ((w :: xs1) # isSortingOfLeft) (sortedRight # isSortingOfRight) | acc = absurdity @{uninhabitedIsPermutationOfNilCons} $ snd isSortingOfLeft
  merge' {left = []} {right = right} ([] # isSortingOfLeft) (sortedRight # isSortingOfRight) | acc = (sortedRight # isSortingOfRight)
  merge' {left = (w :: xs1)} {right = []} (sortedLeft # isSortingOfLeft) (sortedRight # isSortingOfRight) | acc = rewrite plusNilRightNeutral {xs=xs1} in (sortedLeft # isSortingOfLeft)
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
            [] => void $
                  SIsNotZ $
                  plusSuccRightSucc (minRight .#. tailSortedLeft) (minRight .#. tailSortedRight) \=>
                    (cong (plus (minRight .#. tailSortedLeft)) $ ConsAddsOne minRight tailSortedRight) \=>
                    (sym (ConcMerges tailSortedLeft (minRight::tailSortedRight) minRight)) \=>
                    (mergeIsPermutationOfSum minRight)
            (mergedH::mergedT) => let
                ml_rel_any_left: RelatesToAll {a=a} {c=List} rel minLeft tailSortedLeft = head {ysIsCons=Refl {x=minLeft::tailSortedLeft}} $ fst isSortingOfLeft
                mr_rel_any_right = (reflexive {rel=rel} {x=minRight} :: (head {ysIsCons=Refl {x=minRight :: tailSortedRight}} {rel=rel} $ fst isSortingOfRight)) {rel=rel} {x=minRight} {c=List}
                ml_rel_any_right: RelatesToAll {a=a} {c=List} rel minLeft (Prelude.(::) minRight tailSortedRight) = transitive rel_l_r . mr_rel_any_right
                ml_rel_any_lr = (ml_rel_any_left ++ ml_rel_any_right) {rel=rel} {c=List} {a=a} {xs=tailSortedLeft} {ys=minRight::tailSortedRight}
                ml_rel_merged = (ml_rel_any_lr -@-> Ipo {a=a} mergeIsPermutationOfSum) {rel=rel} {c=List} {a=a} {xs=tailSortedLeft++minRight::tailSortedRight} {ys=(mergedH :: mergedT)}
              in (ml_rel_merged {n=mergedH .#. mergedT} (rewrite ConsAddsOne mergedH mergedT in Refl)  :@: mergeIsSorted, transitive @{transitiveIsPermutationOf} (snd isSortingOfLeft ++ snd isSortingOfRight) (minLeft::(Ipo mergeIsPermutationOfSum)))
                -- ml_rel_any_left = head $ fst isSortingOfLeft
                -- mr_rel_any_right = (reflexive {rel=rel} {x=minRight} :: (head {rel=rel} $ fst isSortingOfRight)) {rel=rel} {x=minRight} 
                -- ml_rel_any_right: RelatesToAll rel minLeft (minRight::tailSortedRight) = transitive rel_l_r . mr_rel_any_right
                -- ml_rel_any_lr = (ml_rel_any_left ++ ml_rel_any_right) {rel=rel}
                -- ml_rel_merged = (ml_rel_any_lr -@-> Ipo mergeIsPermutationOfSum) {rel=rel}
                -- (mhInMergedT ** mhInMergedTPrf) = countOccurrences mergedH mergedT
                -- abc = minLeft::(Ipo mergeIsPermutationOfSum)
                -- cde = snd isSortingOfLeft ++ snd isSortingOfRight
              -- in ((ml_rel_merged $ Here mhInMergedTPrf) :@: mergeIsSorted, transitive @{transitiveIsPermutationOf} cde abc)
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
            [] => void $
                  SIsNotZ $
                    (cong (+ (minLeft .#. tailSortedRight)) $ ConsAddsOne minLeft tailSortedLeft) \=>
                    (sym (ConcMerges (minLeft::tailSortedLeft) tailSortedRight minLeft)) \=>
                    (mergeIsPermutationOfSum minLeft)
            (mergedH::mergedT) => let
                mr_rel_any_right: RelatesToAll {c=List} rel minRight tailSortedRight = head $ fst isSortingOfRight
                ml_rel_any_left = (reflexive {rel=rel} {x=minLeft} :: (head {ysIsCons=Refl {x=minLeft :: tailSortedLeft}} {rel=rel} $ fst isSortingOfLeft)) {rel=rel} {x=minLeft} {c=List}
                mr_rel_any_left: RelatesToAll rel minRight (Prelude.(::) minLeft tailSortedLeft) = transitive rel_r_l . ml_rel_any_left
                mr_rel_any_lr = (mr_rel_any_left ++ mr_rel_any_right) {rel=rel} {xs=minLeft::tailSortedLeft} {ys=tailSortedRight}
                mr_rel_merged = (mr_rel_any_lr -@-> Ipo mergeIsPermutationOfSum) {rel=rel} {c=List} {xs=minLeft::tailSortedLeft++tailSortedRight} {ys=(mergedH :: mergedT)}
                cde : (w::xs1 ++ v::ys1) ~@~ (minLeft::tailSortedLeft ++ minRight::tailSortedRight) = snd isSortingOfLeft ++ snd isSortingOfRight
                sumIsPermutationOfMerge: ((mergedH::mergedT) ~@~ (minLeft::tailSortedLeft++tailSortedRight)) = symmetric @{symmetricIsPermutationOf} $ Ipo mergeIsPermutationOfSum
                sumIsPermutationOfMerge' : ((mergedH::mergedT) ~@~ (tailSortedRight ++ minLeft::tailSortedLeft)) = AdditionOfPermutationsCommutes {xs=Prelude.(::) minLeft tailSortedLeft} sumIsPermutationOfMerge
                sumIsPermutationOfMerge'' : ((minRight::mergedH::mergedT) ~@~ (minRight::tailSortedRight ++ minLeft::tailSortedLeft)) = minRight :: sumIsPermutationOfMerge'
                sumIsPermutationOfMerge''' : ((minRight::mergedH::mergedT) ~@~ (minLeft::tailSortedLeft ++ minRight::tailSortedRight)) = AdditionOfPermutationsCommutes {xs=Prelude.(::) minRight tailSortedRight} sumIsPermutationOfMerge''
                abc : (minLeft::tailSortedLeft ++ minRight::tailSortedRight) ~@~ (minRight::mergedH::mergedT) = symmetric @{symmetricIsPermutationOf} sumIsPermutationOfMerge'''
                -- abc = symmetric @{symmetricIsPermutationOf} $
                --   AdditionOfPermutationsCommutes {xs=Prelude.(::) minRight tailSortedRight}
                --     (minRight::(AdditionOfPermutationsCommutes {xs=Prelude.(::) minLeft tailSortedLeft} sumIsPermutationOfMerge))
                -- cde = snd isSortingOfLeft ++ snd isSortingOfRight
              in (mr_rel_merged {n=mergedH .#. mergedT} (rewrite ConsAddsOne mergedH mergedT in Refl)  :@: mergeIsSorted, transitive @{transitiveIsPermutationOf} cde abc)
              --   mr_rel_any_right = head $ fst isSortingOfRight
              --   ml_rel_any_left = (reflexive {rel=rel} {x=minLeft} :: (head {rel=rel} $ fst isSortingOfLeft)) {rel=rel} {x=minLeft} 
              --   mr_rel_any_left: RelatesToAll rel minRight (minLeft::tailSortedLeft) = transitive rel_r_l . ml_rel_any_left
              --   mr_rel_any_lr = (mr_rel_any_left ++ mr_rel_any_right) {rel=rel}
              --   mr_rel_merged = (mr_rel_any_lr -@-> Ipo mergeIsPermutationOfSum) {rel=rel}
              --   (mhInMergedT ** mhInMergedTPrf) = countOccurrences mergedH mergedT
              --   abc = symmetric @{symmetricIsPermutationOf} $ AdditionOfPermutationsCommutes {xs=minRight::tailSortedRight} (minRight::(AdditionOfPermutationsCommutes {xs=minLeft::tailSortedLeft} $ symmetric @{symmetricIsPermutationOf} $ Ipo mergeIsPermutationOfSum))
              --   cde = snd isSortingOfLeft ++ snd isSortingOfRight
              -- in ((mr_rel_merged $ Here mhInMergedTPrf) :@: mergeIsSorted, transitive @{transitiveIsPermutationOf} cde abc)
          )

-- ||| Sort a list in accordance to the linear order induced by rel.
-- ||| This is an implementation of the merge sort algorithm.
-- export
-- mergeSort : (as: List a) ->  DecEq a => (lo: LinearOrder a rel) => (List a) # (IsSortingOf lo as)
-- mergeSort as with (sizeAccessible as)
--   mergeSort as | acc with (split as)
--     mergeSort [] | acc | SplitNil = [] # (Nil,  reflexive @{reflexiveIsPermutationOf})
--     mergeSort [x] | acc | (SplitOne x) = [x] # (Singleton, reflexive @{reflexiveIsPermutationOf})
--     mergeSort (x :: (xs ++ (y :: ys))) | Access acc | (SplitPair x xs y ys) with (mergeSort (x::xs) | acc _ (smallerLeft xs y ys))
--       mergeSort (x :: (xs ++ (y :: ys))) | (Access acc) | (SplitPair x xs y ys) | ([] # cantBe ) = absurdity @{uninhabitedIsPermutationOfConsNil} $ snd cantBe
--       mergeSort (x :: (xs ++ (y :: ys))) | (Access acc) | (SplitPair x xs y ys) | ((z :: zs) # prfZs) with (mergeSort (y::ys) | acc _ (smallerRight xs ys))
--         mergeSort (x :: (xs ++ (y :: ys))) | (Access rec) | (SplitPair x xs y ys) | ((z :: zs) # prfZs) | ([] # cantBe) = absurdity @{uninhabitedIsPermutationOfConsNil} $ snd cantBe
--         mergeSort (x :: (xs ++ (y :: ys))) | (Access rec) | (SplitPair x xs y ys) | ((z :: zs) # prfZs) | ((z' :: zs') # prfZs') = merge' ((z :: zs) # prfZs) ((z' :: zs') # prfZs')
