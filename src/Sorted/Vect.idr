module Sorted.Vect

import Control.Order
import Control.WellFounded
import Data.Linear.Notation
import Data.Nat
import Data.Nat.Views
import Data.Vect
import Decidable.Equality

import Sorted.Prop

public export
data Sorted: (0 lo: LinearOrder a rel) => (Vect n a) -> Type where
    NilIsSorted: Sorted @{lo} Nil
    SingletonIsSorted : Sorted @{lo} [x]
    SeveralAreSorted: (LinearOrder a rel) => (0 _: rel x y) -> (0 _: Sorted @{lo} (y::ys)) -> Sorted @{lo} (x::y::ys)

public export
0 sortedTail : (0 lo: LinearOrder a rel) => Sorted @{lo} (x::xs) -> Sorted @{lo} xs
sortedTail SingletonIsSorted = NilIsSorted
sortedTail (SeveralAreSorted z w) = w

public export
split : Vect n a -@ LPair (Vect (smallHalf n) a) (Vect (largeHalf n) a)
split {n=1 + (1 + m)} (x::y::tail) =
    let (xs # ys) = Sorted.Vect.split tail in
        ( rewrite (smallHalfGrowsEvery2 m) in (x::xs)
        # rewrite (largeHalfGrowsEvery2 m) in (y::ys))
split [] = ([] # [])
split [x] = ([] # [x])

public export
merge: (DecEq a) => (lo: LinearOrder a rel) => (xs: (Vect m a) # (Sorted @{lo})) -> (ys: (Vect n a) # (Sorted @{lo}))
    -> ((Vect (m+n) a) # (Sorted @{lo})) # \merged => (forall j . (Sorted @{lo} (j::subject xs)) -> (Sorted @{lo} (j::subject ys)) -> Sorted @{lo} (j::(subject merged)))
merge ([] # _)  y =  y # (\_ => \a => a)
merge x ([] # _) = rewrite (plusZeroRightNeutral  m) in (x # (\w => \_ => w))
merge {m = S pm} {n = S pn} ((x::xs) # px) ((y::ys) # py) =
    let
        xrely: Either (rel x y) (rel y x) = case decEq x y of
            Yes xEqy => Left (rewrite xEqy in reflexive)
            No xNEqy => connex xNEqy
    in
        case xrely of
            Left vrel =>
                let
                    (xsz # pxz) # f = merge (xs # (sortedTail px)) (y::ys # py)
                in
                    ((x :: xsz) # (f px (SeveralAreSorted @{lo} vrel py))) # (
                        \(SeveralAreSorted xxa xxb) => \(SeveralAreSorted yya yyb) => (SeveralAreSorted xxa $ f xxb $ SeveralAreSorted vrel yyb))
            Right vrel =>
                let
                    ((ysz # pxz) # f) = merge (x::xs # px) (ys # (sortedTail py))
                in
                rewrite sym (eqSucc _ _ (plusSuccRightSucc pm pn)) in
                    (((y :: ysz) # (f (SeveralAreSorted vrel px) py)) # (
                        \(SeveralAreSorted xxa xxb) => \(SeveralAreSorted yya yyb) => (SeveralAreSorted yya $ f (SeveralAreSorted vrel xxb) yyb)))

public export
mergeSort : (DecEq a) => (lo: LinearOrder a rel) => Vect m a -> (Vect m a) # (Sorted @{lo})
mergeSort [] = [] # NilIsSorted
mergeSort [x] = [x] # SingletonIsSorted
mergeSort {m = S (S n)} (x::y::tail) =
    let
        (l # r) = Sorted.Vect.split tail
        l' = mergeSort (assert_smaller (x::y::tail) (x::l))
        r' = mergeSort (assert_smaller (x::y::tail) (y::r))
        (res # _) = merge  l' r'
    in
        rewrite sym $ smallAndLargeHalfMakeWhole n in rewrite plusSuccRightSucc (smallHalf n) (largeHalf n) in res
