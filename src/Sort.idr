module Sort

import Data.Vect
import Data.Nat
import Data.Nat.Order
import Control.Order

%default total

public export
interface (PartialOrder ty rel, StronglyConnex ty rel) => StrongLinearOrder ty rel where

namespace Prop
    public export
    data Prop: (a: Type) -> (a -> Type) -> Type where
        (#): (f: a) -> (0 prf: p f) -> Prop a p

(#) : (a: Type) -> (a-> Type) -> Type
(#) a f = Prop a f

data Sorted: (0 lo: StrongLinearOrder a rel) => (Vect n a) -> Type where
    NilIsSorted: Sorted @{lo} Nil
    SingletonIsSorted : Sorted @{lo} [x]
    SeveralAreSorted: (StrongLinearOrder a rel) => (0 _: rel x y) -> (0 _: Sorted @{lo} (y::ys)) -> Sorted @{lo} (x::y::ys)

subject : a # p -> a
subject (f # prf) = f

0 sortedTail : (0 lo: StrongLinearOrder a rel) => Sorted @{lo} (x::xs) -> Sorted @{lo} xs
sortedTail SingletonIsSorted = NilIsSorted
sortedTail (SeveralAreSorted z w) = w

x : (Vect 4 Nat) # (Sorted {rel = LTE} @{_})
x = [0, 1, 2, 3] # (SeveralAreSorted LTEZero (SeveralAreSorted (LTESucc LTEZero) (SeveralAreSorted (LTESucc (LTESucc LTEZero)) (SingletonIsSorted))))

y : (Vect 3 Nat) # (Sorted {rel = LTE} @{_})
y = [4, 5, 6] # (SeveralAreSorted (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))) (SeveralAreSorted (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))) (SingletonIsSorted)))

data Parity : Nat -> Type where
   Even : {n : _} -> Parity (n + n)
   Odd  : {n : _} -> Parity (S (n + n))

parity : (n : Nat) -> Parity n
parity Z = Even {n = Z}
parity (S Z) = Odd {n = Z}
parity (S (S k)) with (parity k)
  parity (S (S (j + j))) | Even
      = rewrite plusSuccRightSucc j j in Even {n = S j}
  parity (S (S (S (j + j)))) | Odd
      = rewrite plusSuccRightSucc j j in Odd {n = S j}

smallHalf : Nat -> Nat
smallHalf n with (parity n)
    smallHalf (j + j) | Even = j
    smallHalf (S (j + j)) | Odd = j

largeHalf : Nat -> Nat
largeHalf n with (parity n)
    largeHalf (j + j) | Even = j
    largeHalf (S (j + j)) | Odd = S j

smallAndLargeHalfMakeWhole : (n: Nat) -> (smallHalf n + largeHalf n = n)
smallAndLargeHalfMakeWhole n with (parity n)
    smallAndLargeHalfMakeWhole (j + j) | Even = Refl
    smallAndLargeHalfMakeWhole (S (j + j)) | Odd = sym (plusSuccRightSucc j j)

smallHalfGrowsEvery2 : (n: Nat) -> (smallHalf (S (S n)) = S (smallHalf n))
smallHalfGrowsEvery2 n with (parity n)
  smallHalfGrowsEvery2 (j+j) | Even = Refl
  smallHalfGrowsEvery2 (S (j+j)) | Odd = Refl

largeHalfGrowsEvery2 : (n: Nat) -> (largeHalf (S (S n)) = S (largeHalf n))
largeHalfGrowsEvery2 n with (parity n)
  largeHalfGrowsEvery2 (j+j) | Even = Refl
  largeHalfGrowsEvery2 (S (j+j)) | Odd = Refl

0 veclen : (_: Vect n a) -> Nat
veclen _ = n

split : Vect n a -> ((Vect (smallHalf n) a), (Vect (largeHalf n) a))
split [] = ([], [])
split (x :: Nil) = ([], [x])
split (x::y::tail) =
    let (xs, ys) = Sort.split tail in
        ( replace {p = \k => Vect k a} (sym (smallHalfGrowsEvery2 (veclen tail))) (x::xs)
        , replace {p = \k => Vect k a} (sym (largeHalfGrowsEvery2 (veclen tail))) (y::ys))

sucIsEqual' : {m, n: Nat} -> n=m -> S n = S m
sucIsEqual' Refl = Refl

plusZeroIsSame: (m: Nat) -> (m+0 = m)
plusZeroIsSame 0 = Refl
plusZeroIsSame (S k) = rewrite plusZeroIsSame k in (sucIsEqual' Refl)

merge: (lo: StrongLinearOrder a rel) => ((Vect m a) # (Sorted @{lo})) -> ((Vect n a) # (Sorted @{lo})) -> ((Vect (m+n) a) # (Sorted @{lo}))
merge ([] # _)  y =  y
merge x ([] # _) = replace {p = \m => (Vect m a) # (Sorted @{lo})} (sym (plusZeroIsSame _)) x
merge ((x::xs) # px) ((y::ys) # py) =
    case order @{_} x y of
        Left vrel =>
            let
                (xsz # pxz) = merge @{_} (xs # (sortedTail px)) (y::ys # py)
                0 srtd: Sorted @{lo} (x:: xsz) = ?merge_0
            in
                (x :: xsz) # srtd
        Right vrel =>
            let
                (ysz # pxz) = merge @{_} (x::xs # px) (ys # (sortedTail py))
                res = replace {p = \swe => Vect swe a} (sucIsEqual' (plusSuccRightSucc _ _)) (y::ysz)
                0 srtd: Sorted @{lo} res = ?merge_1
            in
                res # srtd

mergeSort : (lo: StrongLinearOrder a rel) => Vect m a -> (Vect m a) # (Sorted @{lo})
mergeSort [] = [] # NilIsSorted
mergeSort [x] = [x] # SingletonIsSorted
mergeSort v @ (_::_::xs) =
    let
        (l, r) = Sort.split v
        l' = mergeSort @{lo} (assert_smaller v l)
        r' = mergeSort @{lo} (assert_smaller v r)
        res = merge @{lo} l' r'
    in
        replace {p = \m => (Vect m a) # (Sorted @{lo})} (smallAndLargeHalfMakeWhole _) res

-- n > smallHalf n
-- n > largelHalf n
--
-- 0 0 0
-- 1 0 1
-- 2 1 1
-- 3 1 2
-- 4 2 2
-- 5 2 3
-- 6 3 3
-- 7 3 4
-- 8 4 4
-- 9 4 5
