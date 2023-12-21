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

import Sorted.Prop

-- %unbound_implicits off
%default total
%search_timeout 100

public export
data Sorted: {0 a: Type} -> {0 rel: Rel a} -> (0 lo: LinearOrder a rel) => List a -> Type where
    NilIsSorted: {0 a: Type} -> {0 rel: Rel a} -> (0 lo: LinearOrder a rel) => Sorted @{lo} Nil
    SingletonIsSorted : {0 a: Type} -> {x: a} -> {0 rel: Rel a} -> (0 lo: LinearOrder a rel) => Sorted @{lo} [x]
    SeveralAreSorted: {0 a: Type} -> {x, y: a} -> {ys: List a} -> {0 rel: Rel a} -> (0 lo: LinearOrder a rel) => rel x y -> Sorted @{lo} (y::ys) -> Sorted @{lo} (x::y::ys)

public export
sortedTail : {0 a: Type} -> {0 x: a} -> {0 xs: List a} -> {0 rel: Rel a} -> (0 lo: LinearOrder a rel) => Sorted @{lo} (x::xs) -> Sorted @{lo} xs
sortedTail SingletonIsSorted = NilIsSorted
sortedTail (SeveralAreSorted z w) = w

||| A proof that some element occurs in a list n number of times.
public export
data Occurs : {0 a: Type} -> a -> Nat -> List a -> Type where
     ||| A proof that the element is at the head of the list
     Here : {0 a: Type} -> {0 occurrent: a} -> {0 occurrencies: Nat} -> {0 occurrences: List a} -> Occurs occurrent occurrencies occurrences ->  Occurs occurrent (1+occurrencies) (occurrent :: occurrences)
     ||| A proof that the element is in the tail of the list
     There : {0 a: Type} -> {0 occurrent, notTheOccurrent: a} -> {0 occurrencies: Nat} -> {0 occurrences: List a} -> Occurs occurrent occurrencies occurrences -> Not (occurrent=notTheOccurrent) -> Occurs occurrent occurrencies (notTheOccurrent :: occurrences)
     ||| A proof that the element is not in the empty list
     Nowhere: {0 a: Type} -> {0 occurrent: a} -> Occurs occurrent 0 []

SameOccurrent : {0 a: Type} -> {0 occurrent, another: a} -> {0 occurrencies: Nat} -> {0 occurrences: List a} -> Occurs occurrent occurrencies occurrences -> another = occurrent -> Occurs another occurrencies occurrences
SameOccurrent x prf = rewrite prf in x

OccursTheSameNumberOfTimes : {0 a: Type} -> {0 x: a} -> {0 m, n: Nat} -> {0 xs: List a} -> Occurs x m xs -> Occurs x n xs -> m = n
OccursTheSameNumberOfTimes Nowhere Nowhere = Refl
OccursTheSameNumberOfTimes (There _ f) (Here _) = void $ f Refl
OccursTheSameNumberOfTimes (There y _) (There z _) = OccursTheSameNumberOfTimes y z
OccursTheSameNumberOfTimes (Here _) Nowhere impossible
OccursTheSameNumberOfTimes (Here pm) (Here pn) = cong S $ OccursTheSameNumberOfTimes pm pn
OccursTheSameNumberOfTimes (Here _) (There _ f) = void $ f Refl

public export
[uninhabitedOccursAtLeastOnceInNil] {0 a: Type} -> {0 x: a} -> Uninhabited (Occurs x (S _) []) where
  uninhabited Here impossible

public export
[uninhabitedOccursZeroTimesWhenHeadMatches] {0 a: Type} -> {0 x: a} -> {0 xs: List a} -> Uninhabited (Occurs x 0 (x::xs)) where
  uninhabited (There _ f) = f Refl

public export
countOccurrences: {0 a: Type} -> DecEq a => (x: a) -> (l: List a) -> DPair Nat (\n => Occurs x n l)
countOccurrences x [] = (0 ** Nowhere)
countOccurrences x (y :: xs) with (countOccurrences x xs)
  countOccurrences x (y :: xs) | (f ** prf) with (decEq x y)
    countOccurrences x (y :: xs) | (f ** prf) | (Yes z) = (S f ** rewrite sym z in Here prf)
    countOccurrences x (y :: xs) | (f ** prf) | (No contra) = (f ** There prf contra)

0 IsPermutationOf : {0 a: Type} -> Rel (List a)
IsPermutationOf original permutation = {anElement: a} -> {occurrenciesInOriginal, occurrenciesInPermutation: Nat} -> (occursInOriginal: Occurs anElement occurrenciesInOriginal original) -> (occursInPermutation: Occurs anElement occurrenciesInPermutation permutation) -> occurrenciesInOriginal = occurrenciesInPermutation

public export
[uninhabitedIsPermutationOfConsNil] {0 a: Type} -> {0 x: a} -> {0 xs: List a} -> DecEq a => Uninhabited (IsPermutationOf (x::xs) []) where
    uninhabited isPermutationOfConsNil = absurdity $ isPermutationOfConsNil (Here $ let (0 ** xInXsPrf) = countOccurrences x xs in xInXsPrf) Nowhere

public export
[uninhabitedIsPermutationOfNilCons] {0 a: Type} -> {0 x: a} -> {0 xs: List a} -> DecEq a => Uninhabited (IsPermutationOf [] (x::xs)) where
    uninhabited isPermutationOfNilCons = absurdity $ isPermutationOfNilCons Nowhere (Here $ let (0 ** xInXsPrf) = countOccurrences x xs in xInXsPrf)

public export
[reflexiveIsPermutationOf] {0 a: Type} -> Reflexive (List a) IsPermutationOf where
    reflexive Nowhere Nowhere = Refl
    reflexive (There y f) (Here z) = void $ f Refl
    reflexive (There y f) (There z g) = reflexive @{reflexiveIsPermutationOf} y z
    reflexive (Here _) Nowhere impossible
    reflexive (Here pm) (Here pn) = cong S $ reflexive @{reflexiveIsPermutationOf} pm pn
    reflexive (Here _) (There _ f) = void $ f Refl

public export
[transitiveIsPermutationOf] {0 a: Type} -> DecEq a => Transitive (List a) IsPermutationOf where
    transitive {x=original} {y=permutation} {z=anotherPermutation} isPermutationOP isPermutationPA occursInOriginal occursInAnother =
      let
        (_ ** occursInPermutation) = countOccurrences anElement permutation
      in transitive (isPermutationOP occursInOriginal occursInPermutation) (isPermutationPA occursInPermutation occursInAnother)

public export
[symmetricIsPermutationOf] {0 a: Type} -> Symmetric (List a) IsPermutationOf where
    symmetric isPermutation occurrsInPermutation occurrsInOriginal= sym $ isPermutation occurrsInOriginal occurrsInPermutation

SingletonPermutationIsIdentity : {0 a: Type} -> {x, y: a} -> DecEq a => IsPermutationOf [x] [y] -> [x] = [y]
SingletonPermutationIsIdentity isPermutationOfXY with (decEq x y)
  SingletonPermutationIsIdentity isPermutationOfXY | (Yes prf) = cong (\e => [e]) prf
  SingletonPermutationIsIdentity isPermutationOfXY | (No contra) with (isPermutationOfXY (Here Nowhere) (There Nowhere contra))
    SingletonPermutationIsIdentity isPermutationOfXY | (No contra) | _ impossible

PermutationOfCons : {0 a: Type} -> {x: a} -> {0 xs, ys: List a} -> DecEq a => IsPermutationOf (x::xs) (x::ys) -> IsPermutationOf xs ys
PermutationOfCons f occursInOriginal occursInPermutation with (decEq anElement x)
  PermutationOfCons f occursInOriginal occursInPermutation | (Yes anElementEqX) = cong pred $ f (Here $ SameOccurrent occursInOriginal $ sym anElementEqX) (Here $ SameOccurrent occursInPermutation $ sym anElementEqX)
  PermutationOfCons f occursInOriginal occursInPermutation | (No anElementNEqX) = f (There occursInOriginal anElementNEqX) (There occursInPermutation anElementNEqX)

[uninhabitedIsPermutationOfConsConsXsConsNil] {0 a: Type} -> {x, x', y: a} -> {xs: List a} -> DecEq a => Uninhabited (IsPermutationOf (x::x'::xs) [y]) where
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

0 IsSortingOf : {0 a: Type} -> {0 rel: Rel a} -> (0 lo: LinearOrder a rel) => Rel (List a)
IsSortingOf as = Sorted @{lo} && IsPermutationOf as

[uninhabitedIsSortingOfEmptyCons] {0 a: Type} -> {0 rel: Rel a} -> {0 x:a} -> {0 xs: List a} -> DecEq a => (lo: LinearOrder a rel) => Uninhabited (IsSortingOf @{lo} [] (x::xs)) where
    uninhabited (_, isPermutationOfNilXXs) = absurdity @{uninhabitedIsPermutationOfNilCons} isPermutationOfNilXXs

public export
{0 a: Type} -> {0 rel: Rel a} -> DecEq a => (lo: LinearOrder a rel) => Transitive (List a) (IsSortingOf @{lo}) where
    transitive (_, s) (w, t) = (w, transitive @{transitiveIsPermutationOf} s t)

HeadIsInfimum : {e': a} -> {lo: LinearOrder a rel} -> Sorted @{lo} (e::es) -> Occurs e' (S n) es -> rel e e'
HeadIsInfimum SingletonIsSorted (Here _) impossible
HeadIsInfimum SingletonIsSorted (There _ _) impossible
HeadIsInfimum SingletonIsSorted Nowhere impossible
HeadIsInfimum {n=n} {e = e} {es = (e' :: es)} {e' = e'} (SeveralAreSorted relEE' sortedE'Es) (Here x) = relEE'
HeadIsInfimum {n=n} {e = e} {es = (e'' :: es)} {e' = e'} (SeveralAreSorted relEE'' sortedE''Es) (There occursE'SnEs _) = transitive relEE'' $HeadIsInfimum sortedE''Es occursE'SnEs

NotHere : Occurs x (S n) (other::xs) -> Not (x=other) -> Occurs x (S n) xs
NotHere (Here _) f = void $ f Refl
NotHere (There y _) _ = y

ElemOfPermutation : {e: a} -> {n: Nat} -> {xs, ys: List a} -> DecEq a => IsPermutationOf xs ys -> Occurs e (S n) xs -> Occurs e (S n) ys
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
          allAboutX = replace
            {p = \yyy => {anElement: a} -> {occurrenciesInOriginal, occurrenciesInPermutation: Nat} -> Occurs anElement occurrenciesInOriginal (x :: (x' :: xs)) -> Occurs anElement occurrenciesInPermutation (yyy::y'::ys) -> occurrenciesInOriginal = occurrenciesInPermutation}
            (sym xEqY)
            isPermutationOfXsYs
          allButX = PermutationOfCons allAboutX
          mimi = antisymmetric @{antisymmetricIsSortingOf {lo=lo}} {rel = IsSortingOf {a=a} {rel=rel} {lo=lo}} (sortedY'Ys, allButX) (sortedX'Xs, symmetric @{symmetricIsPermutationOf} allButX)
        in cong2 Prelude.(::) xEqY mimi
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


-- lengthSuc : (xs : List a) -> (y : a) -> (ys : List a) ->
--             length (xs ++ (y :: ys)) = S (length (xs ++ ys))
-- lengthSuc [] _ _ = Refl
-- lengthSuc (x :: xs) y ys = cong S (lengthSuc xs y ys)

-- lengthLT : (xs : List a) -> (ys : List a) ->
--            LTE (length xs) (length (ys ++ xs))
-- lengthLT xs [] = reflexive {x = length xs}
-- lengthLT xs (x :: ys) = lteSuccRight (lengthLT _ _)

-- smallerLeft : (ys : List a) -> (y : a) -> (zs : List a) ->
--               LTE (S (S (length ys))) (S (length (ys ++ (y :: zs))))
-- smallerLeft [] y zs = LTESucc (LTESucc LTEZero)
-- smallerLeft (z :: ys) y zs = LTESucc (smallerLeft ys _ _)

-- smallerRight : (ys : List a) -> (zs : List a) ->
--                LTE (S (S (length zs))) (S (length (ys ++ (y :: zs))))
-- smallerRight ys zs = rewrite lengthSuc ys y zs in
--                      (LTESucc (LTESucc (lengthLT _ _)))

-- covering
-- mergeSort : DecEq a => (lo: LinearOrder a rel) => (as: List a) -> (List a) # (SortingOf @{lo} as)
-- mergeSort as with (sizeAccessible as)
--   mergeSort as | acc with (split as)
--     mergeSort [] | acc | SplitNil = [] # (NilIsSorted, reflexive_IsPermutationOf)
--     mergeSort [x] | acc | (SplitOne x) = [x] # (SingletonIsSorted, reflexive_IsPermutationOf)
--     mergeSort (x :: (xs ++ (y :: ys))) | Access acc | (SplitPair x xs y ys) with (mergeSort (x::xs) | acc _ (smallerLeft xs y ys))
--       mergeSort (x :: (xs ++ (y :: ys))) | (Access acc) | (SplitPair x xs y ys) | ([] # cantBe ) = absurdity @{uninhabitedIsPermutationOfConsNil} $ snd cantBe
--       mergeSort (x :: (xs ++ (y :: ys))) | (Access acc) | (SplitPair x xs y ys) | ((z :: zs) # prfZs) with (mergeSort (y::ys) | acc _ (smallerRight xs ys))
--         mergeSort (x :: (xs ++ (y :: ys))) | (Access rec) | (SplitPair x xs y ys) | ((z :: zs) # prfZs) | ([] # cantBe) = absurdity @{uninhabitedIsPermutationOfConsNil} $ snd cantBe
--         mergeSort (x :: (xs ++ (y :: ys))) | (Access rec) | (SplitPair x xs y ys) | ((z :: zs) # prfZs) | ((z' :: zs') # prfZs') = merge' ((z :: zs) # prfZs) ((z' :: zs') # prfZs') where
--             merge' : (left': (List a) # (SortingOf @{lo} left)) -> (right': (List a) # (SortingOf @{lo} right)) -> (List a) # (SortingOf @{lo} (left ++ right))
--             merge' ([] # pleft') (right' # pright') = right' # let
--                 (NilIsSorted, nilIsPermutationOfLeft) = pleft'
--                 (rightIsSorted, rightIsPermutation) = pright'
--               in (rightIsSorted, ?merge'_rhs_4)
--             merge' ((w :: xs1) # pleft') (right' # pright') = ?merge'_rhs_2

            -- merge left right where
            --     merge : (lo: LinearOrder a rel) => {ls, rs: List a} -> (List a) # (SortingOf @{lo} ls) -> (List a) # (SortingOf @{lo} rs) -> (List a) # (SortingOf @{lo} (ls ++ rs))
            --     merge {ls = []} {rs = rs} ([] # _) f = f
            --     merge {ls = (w :: zs)} {rs = []} ([] # prf) (f # z) = ?merge_rhs_9
            --     merge {ls = (w :: zs)} {rs = v :: xs1} ([] # prf) (f # z) = ?merge_rhs_10
            --     merge {ls} {rs = rs} ((z :: zs) # prf) srs = ?merge_rhs_5

-- mergeSort as with (split as)
--   mergeSort [] | SplitNil = [] # (NilIsSorted, reflexive_IsPermutationOf)
--   mergeSort [x] | (SplitOne x) = [x] # (SingletonIsSorted, reflexive_IsPermutationOf)
--   mergeSort (x :: (xs ++ (y :: ys))) | (SplitPair x xs y ys) with (sizeAccessible (x::xs))
--     mergeSort (x :: (xs ++ (y :: ys))) | (SplitPair x xs y ys) | (Access rec) = ?mergeSort_rhs_rhss_2_rhs2_0

-- public export
-- allAppend : {0 p : a -> Type} -> {xs : List a} -> {ys: List a} -> All p xs -> All p ys -> All p (xs ++ ys)
-- allAppend [] y = y
-- allAppend (x :: z) y = x :: allAppend z y

-- public export
-- splitAll : {0 p : a -> Type} -> {xs : List a} -> {ys: List a} -> All p (xs ++ ys) -> (All p xs, All p ys)
-- splitAll {xs=[]} x = ([], x)
-- splitAll {xs=x::xs'} (xy::xys) = let (p, q) = splitAll xys in (xy::p, q)

-- public export
-- split : (xs: List a) -> (List (smallHalf n) a, List (largeHalf n) a) # (IsPermutationOf xs . rewrite sym (smallAndLargeHalfMakeWhole n) in uncurry List.(++))
-- split {n=1 + (1 + m)} (x::y::tail) =
--     let
--         ((xs, ys) # perm) = Sorted.List.split tail
--     in
--         ( rewrite (smallHalfGrowsEvery2 m) in (x::xs)
--         , rewrite (largeHalfGrowsEvery2 m) in (y::ys)) # let
--             (perml, permr): (All (\elem => Elem elem tail) (xs++ys), All (\elem => Elem elem (xs++ys)) tail) = rewrite smallAndLargeHalfMakeWhole m in perm
--             -- (xsInTail, ysInTail): (All (\elem => Elem elem tail) xs, All (\elem => Elem elem tail) ys) = ?perml_0
--             -- xxsInRes = Here :: mapProperty (\z => There (There z)) xsInTail
--             -- yysInRes = There Here :: mapProperty (\z => There (There z)) ysInTail
--             -- allInRes: All (\elem => Elem elem (x::xs ++ y::ys)) (x::y::tail) = allAppend xxsInRes yysInRes

--             -- (xsInResR, ysInResR) = splitAll permr
--             -- xxsInResR = Here :: mapProperty (\z => There (There z)) xsInResR
--             -- yysInResR = There Here :: mapProperty (\z => There (There z)) ysInResR
--             -- allInResR: All (\elem => Elem elem (x::y::tail)) (x::xs ++ y::ys) = allAppend xxsInResR yysInResR
--         in ?split_0 -- ( allInRes, allInResR )
-- split [] = ([] , []) # ([], [])
-- split [x] = ([] , [x]) # ([Here], [Here])

-- public export
-- merge: (DecEq a) => (lo: LinearOrder a rel) => (xs: (List a) # (Sorted @{lo})) -> (ys: (List a) # (Sorted @{lo}))
--     -> List a # (
--         Sorted @{lo} &&
--         (\merged => ((Sorted @{lo} (john::subject xs)) -> (Sorted @{lo} (john::subject ys)) -> Sorted @{lo} (john::merged))) &&
--         (\merged => len merged = (len $ subject xs) + (len $ subject ys))
--        )
-- merge ([] # _)  (y # py) =  y # (py, \_ => \a => a)
-- merge (x # px) ([] # _) = x # (px, \w => \_ => w)
-- merge ((x::xs) # px) ((y::ys) # py) =
--     let
--         xrely: Either (rel x y) (rel y x) = case decEq x y of
--             Yes xEqy => Left (rewrite xEqy in reflexive)
--             No xNEqy => connex xNEqy
--     in
--         case xrely of
--             Left vrel =>
--                 let
--                     xsz # props = merge (xs # (sortedTail px)) (y::ys # py)
--                 in
--                     (x :: xsz) # let
--                         (pxz, f) = props
--                     in ((f px (SeveralAreSorted vrel py)), (
--                         \(SeveralAreSorted xxa xxb) => \(SeveralAreSorted yya yyb) => (SeveralAreSorted xxa $ f xxb $ SeveralAreSorted vrel yyb)))
--             Right vrel =>
--                 let
--                     ysz # props = merge (x::xs # px) (ys # (sortedTail py))
--                 in
--                     (y :: ysz) # let
--                         (pxz, f) = props
--                     in ((f (SeveralAreSorted vrel px) py), (
--                         \(SeveralAreSorted xxa xxb) => \(SeveralAreSorted yya yyb) => (SeveralAreSorted yya $ f (SeveralAreSorted vrel xxb) yyb)))

-- onlyNilHasLength0 : {x: List a} -> (length x = 0) -> (x = [])
-- onlyNilHasLength0 {x = []} _ = Refl
-- onlyNilHasLength0 {x = (_ :: _)} prf = void $ uninhabited prf

-- merge : (DecEq a) => (lo: LinearOrder a rel) => (List a # SortingOf {lo} left) -> (List a # SortingOf {lo} right) -> (List a # SortingOf {lo} (left ++ right))
-- merge ([] # prf) (f # x) = f # let
--         (nilIsSorted, nilIsSublistOfAnything, lengthOfLeftEq0) = prf
--         leftEqNil = onlyNilHasLength0 lengthOfLeftEq0
--         (fIsSorted, fIsSublistOfRight, lengthOfRghtEqLengthF) = x
--         helper2 = \y => cong (\a => subject (countOccurrences y a)) $ cong (\a => a ++ right) $ sym leftEqNil
--     in (fIsSorted, (?merge_3, ?merge_4))
-- merge ((x :: xs) # prf) y = ?merge_rhs_2

-- public export
-- mergeSort : (DecEq a) => (lo: LinearOrder a rel) => (as: List a) -> (List a) # (SortingOf {lo} as)
-- mergeSort as with (split as)
--   mergeSort [] | SplitNil = [] # (NilIsSorted, ([], Refl))
--   mergeSort [x] | (SplitOne x) = [x] # (SingletonIsSorted, ([Refl], Refl))
--   mergeSort (x :: (xs ++ (y :: ys))) | (SplitPair x xs y ys) with (mergeSort {lo} (x::xs))
--     mergeSort (x :: (xs ++ (y :: ys))) | (SplitPair x xs y ys) | (f # prf) with (mergeSort {lo} (y::ys))
--       mergeSort (x :: (xs ++ (y :: ys))) | (SplitPair x xs y ys) | (f # (v, s)) | (z # w) with (0)
--         mergeSort (x :: (xs ++ (y :: ys))) | (SplitPair x xs y ys) | (f # (v, s)) | (z # w) | with_pat = ?mergeSort_0_rhs0_2_rhs2_0_rhs0_2_rhs2

-- with (split as)
--   mergeSort [] | SplitNil = [] # (NilIsSorted, ([], Refl))
--   mergeSort [x] | (SplitOne x) = [x] # (SingletonIsSorted, ([Refl], Refl))
--   mergeSort (x :: (ys ++ (y :: zs))) | (SplitPair x ys y zs) =
--     let
--         xrely: Either (rel x y) (rel y x) = case decEq x y of
--             Yes xEqy => Left (rewrite xEqy in reflexive)
--             No xNEqy => connex xNEqy
--     in
--         -- (l' # sl') = mergeSort {lo} (assert_smaller (x::y::tail) (x::l))
--         -- (r' # sr') = mergeSort {lo} (assert_smaller (x::y::tail) (y::r))
--         -- (res # _) = merge {lo} (l' # let (sll', _) = sl' in sll') (r' # let (slr', _) = sr' in slr')
--     case xrely of
--             Left vrel => ?mergeSort_0
--             Right vrel => ?mergeSort_1
