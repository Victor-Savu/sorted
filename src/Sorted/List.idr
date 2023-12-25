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
sortedHead : (0 lo: LinearOrder a rel) => Transitive a rel => Sorted @{lo} (x::xs) -> RelatesToAll rel x xs
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

public export
HeadIsInfimum : {e': a} -> (lo: LinearOrder a rel) => Sorted @{lo} (e::es) -> Occurs e' (S n) es -> rel e e'
HeadIsInfimum SingletonIsSorted (Here _) impossible
HeadIsInfimum SingletonIsSorted (There _ _) impossible
HeadIsInfimum SingletonIsSorted Nowhere impossible
HeadIsInfimum {n=n} {e = e} {es = (e' :: es)} {e' = e'} (SeveralAreSorted relEE' sortedE'Es) (Here x) = relEE'
HeadIsInfimum {n=n} {e = e} {es = (e'' :: es)} {e' = e'} (SeveralAreSorted relEE'' sortedE''Es) (There occursE'SnEs _) = transitive relEE'' $ HeadIsInfimum sortedE''Es occursE'SnEs

NotHere : Occurs x (S n) (other::xs) -> Not (x=other) -> Occurs x (S n) xs
NotHere (Here _) f = void $ f Refl
NotHere (There y _) _ = y

ElemOfPermutation : {e: a} -> {n: Nat} -> {xs, ys: List a} -> DecEq a => xs ~@~ ys -> Occurs e (S n) xs -> Occurs e (S n) ys
ElemOfPermutation {n} {xs} {ys} isPermutationOfXsYs eInXs with (countOccurrences e ys)
  ElemOfPermutation {xs = xs} {ys = ys} isPermutationOfXsYs eInXs | (0 ** snd) with (isPermutationOfXsYs eInXs snd)
    ElemOfPermutation {xs = xs} {ys = ys} isPermutationOfXsYs eInXs | (0 ** snd) | _ impossible
  ElemOfPermutation {n} {xs = xs} {ys = ys} isPermutationOfXsYs eInXs | ((S k) ** snd) with (isPermutationOfXsYs eInXs snd)
    ElemOfPermutation {n} {xs = xs} {ys = ys} isPermutationOfXsYs eInXs | ((S n) ** snd) | Refl = snd

covering
public export
[antisymmetricIsSortingOf] {0 a: Type} -> {0 rel: Rel a} -> DecEq a => (lo: LinearOrder a rel) => Antisymmetric (List a) (IsSortingOf @{lo}) where
    antisymmetric {x=[]} {y=[]} (NilIsSorted, isPermutationOfXsYs) (NilIsSorted, _) = Refl
    antisymmetric {x=[x]} {y=[]} (NilIsSorted, isPermutationOfXsYs) (SingletonIsSorted, _) = absurdity @{uninhabitedIsPermutationOfConsNil} isPermutationOfXsYs
    antisymmetric {x=(x :: (x' :: xs))} {y=[]} (NilIsSorted, isPermutationOfXsYs) ((SeveralAreSorted relXX' sortedX'Xs), _) = absurdity @{uninhabitedIsPermutationOfConsNil} isPermutationOfXsYs
    antisymmetric {x=[]} {y=[y]} (SingletonIsSorted, isPermutationOfXsYs) (NilIsSorted, isPermutationOfYsXs) = absurdity @{uninhabitedIsPermutationOfConsNil} isPermutationOfYsXs
    antisymmetric {x=[x]} {y=[y]} (SingletonIsSorted, isPermutationOfXsYs) (SingletonIsSorted, _) = (SingletonPermutationIsIdentity isPermutationOfXsYs)
    antisymmetric {x=(x :: (x' :: xs))} {y=[y]} (SingletonIsSorted, isPermutationOfXsYs) ((SeveralAreSorted relXX' sortedX'Xs), _) = absurdity @{uninhabitedIsPermutationOfConsConsXsConsNil} isPermutationOfXsYs
    antisymmetric {x=[]} {y=(y :: (y' :: ys))} ((SeveralAreSorted relYY' sortedY'Ys), isPermutationOfXsYs) (isSortedXs, isPermutationOfYsXs) = absurdity @{uninhabitedIsPermutationOfConsNil} isPermutationOfYsXs
    antisymmetric {x=[x]} {y=(y :: (y' :: ys))} ((SeveralAreSorted relYY' sortedY'Ys), isPermutationOfXsYs) (isSortedXs, isPermutationOfYsXs) = absurdity @{uninhabitedIsPermutationOfConsConsXsConsNil} isPermutationOfYsXs
    antisymmetric {x=(x :: (x' :: xs))} {y=(y :: (y' :: ys))} ((SeveralAreSorted relYY' sortedY'Ys), isPermutationOfXsYs) ((SeveralAreSorted relXX' sortedX'Xs), isPermutationOfYsXs) with (decEq x y)
      antisymmetric {x=(x :: (x' :: xs))} {y=(y :: (y' :: ys))} ((SeveralAreSorted relYY' sortedY'Ys), isPermutationOfXsYs) ((SeveralAreSorted relXX' sortedX'Xs), isPermutationOfYsXs) | (Yes xEqY) =
        let
          allButX = PermutationOfCons $ replace
            {p = \yyy => {anElement: a} -> {occurrenciesInOriginal, occurrenciesInPermutation: Nat} -> Occurs anElement occurrenciesInOriginal (x :: (x' :: xs)) -> Occurs anElement occurrenciesInPermutation (yyy::y'::ys) -> occurrenciesInOriginal = occurrenciesInPermutation}
            (sym xEqY)
            isPermutationOfXsYs
        in cong2 Prelude.(::) xEqY $ antisymmetric @{antisymmetricIsSortingOf {lo=lo}} {rel = IsSortingOf {a=a} {rel=rel} {lo=lo}} (sortedY'Ys, allButX) (sortedX'Xs, symmetric @{symmetricIsPermutationOf} allButX)
      antisymmetric {x=(x :: (x' :: xs))} {y=(y :: (y' :: ys))} ((SeveralAreSorted relYY' sortedY'Ys), isPermutationOfXsYs) ((SeveralAreSorted relXX' sortedX'Xs), isPermutationOfYsXs) | (No xNEqY) with (connex {rel=rel} @{%search} xNEqY)
        antisymmetric {x=(x :: (x' :: xs))} {y=(y :: (y' :: ys))} ((SeveralAreSorted relYY' sortedY'Ys), isPermutationOfXsYs) ((SeveralAreSorted relXX' sortedX'Xs), isPermutationOfYsXs) | (No xNEqY) | (Left relXY) =
          let
            sortedYY'Ys : Sorted (y::y'::ys) = SeveralAreSorted relYY' sortedY'Ys
            (_ ** timesXOccursInX'Xs) = countOccurrences x (x'::xs)
            xInY'Ys : Occurs x (S _) (y'::ys) = NotHere (ElemOfPermutation isPermutationOfXsYs $ Here timesXOccursInX'Xs) xNEqY
            nailInTheCoffin : rel y x = HeadIsInfimum sortedYY'Ys xInY'Ys
          in void $ xNEqY $ antisymmetric @{%search} relXY nailInTheCoffin
        antisymmetric {x=(x :: (x' :: xs))} {y=(y :: (y' :: ys))} ((SeveralAreSorted relYY' sortedY'Ys), isPermutationOfXsYs) ((SeveralAreSorted relXX' sortedX'Xs), isPermutationOfYsXs) | (No xNEqY) | (Right relYX) =
          let
            sortedXX'Xs : Sorted (x::x'::xs) = SeveralAreSorted relXX' sortedX'Xs
            (_ ** timesYOccursInY'Ys) = countOccurrences y (y'::ys)
            yInX'Xs : Occurs y (S _) (x'::xs) = NotHere (ElemOfPermutation isPermutationOfYsXs $ Here timesYOccursInY'Ys) (\yEqX => xNEqY $ sym yEqX)
            nailInTheCoffin : rel x y = HeadIsInfimum sortedXX'Xs yInX'Xs
          in void $ xNEqY $ antisymmetric @{%search}  nailInTheCoffin relYX


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

-- The sorting of a list starts with the minimum element. The If we have a sorting 


covering
merge' : (lo: LinearOrder a rel) => {left, right: List a} -> (left': (List a) # (IsSortingOf @{lo}  left)) -> (right': (List a) # (IsSortingOf @{lo}  right)) -> DecEq a => (List a) # (IsSortingOf @{lo} (left ++ right))
merge' {left = []} {right = right} ((w :: xs1) # isSortingOfLeft) _ = absurdity @{uninhabitedIsPermutationOfNilCons} $ snd isSortingOfLeft
merge' {left = []} {right = right} ([] # isSortingOfLeft) theSortingOfRight = theSortingOfRight
merge' {left = (w :: xs1)} {right = []} theSortingOfLeft _ = rewrite sameasitis {xs=(w::xs1)} in theSortingOfLeft
merge' {left = (w :: xs1)} {right = (v :: ys1)} ([] # isSortingOfLeft) (sortedRight # isSortingOfRight) = absurdity @{uninhabitedIsPermutationOfConsNil} $ snd isSortingOfLeft
merge' {left = (w :: xs1)} {right = (v :: ys1)} ((minLeft :: tailSortedLeft) # isSortingOfLeft) ([] # isSortingOfRight) = absurdity @{uninhabitedIsPermutationOfConsNil} $ snd isSortingOfRight
merge' {left = (w :: xs1)} {right = (v :: ys1)} ((minLeft :: tailSortedLeft) # isSortingOfLeft) ((minRight::tailSortedRight) # isSortingOfRight) =
  let
    disc : Either (rel minLeft minRight) (rel minRight minLeft) = case (decEq minLeft minRight) of
      (Yes mlEqMr) => Right $ rewrite mlEqMr in reflexive
      (No contra) => connex contra
  in case disc of
    (Left rel_l_r) =>
      let
        merged # prf = merge'
          (tailSortedLeft  # (sortedTail $ fst isSortingOfLeft, reflexive @{reflexiveIsPermutationOf}))
          ((minRight::tailSortedRight) # (fst isSortingOfRight, reflexive @{reflexiveIsPermutationOf}))
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
        merged # prf = merge'
          ((minLeft::tailSortedLeft) # (fst isSortingOfLeft, reflexive @{reflexiveIsPermutationOf}))
          (tailSortedRight  # (sortedTail $ fst isSortingOfRight, reflexive @{reflexiveIsPermutationOf}))
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

covering
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
