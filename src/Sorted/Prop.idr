module Sorted.Prop

import Data.Nat
import Data.Nat.Views

%default total

public export
smallHalf : Nat -> Nat
smallHalf n with (half n)
    smallHalf (j + j) | HalfEven j = j
    smallHalf (1 + (j + j)) | HalfOdd j = j

public export
largeHalf : Nat -> Nat
largeHalf n with (half n)
    largeHalf (j + j) | HalfEven j = j
    largeHalf (1 + (j + j)) | HalfOdd j = S j

export
smallAndLargeHalfMakeWhole : (n: Nat) -> (smallHalf n + largeHalf n = n)
smallAndLargeHalfMakeWhole n with (half n)
    smallAndLargeHalfMakeWhole (j + j) | HalfEven j = Refl
    smallAndLargeHalfMakeWhole (1 + (j + j)) | HalfOdd j = sym (plusSuccRightSucc j j)

export
smallHalfGrowsEvery2 : (n: Nat) -> (smallHalf (S (S n)) = S (smallHalf n))
smallHalfGrowsEvery2 n with (half n)
    smallHalfGrowsEvery2 _ | HalfOdd j = Refl
    smallHalfGrowsEvery2 _ | HalfEven (S j) = Refl
    smallHalfGrowsEvery2 _ | HalfEven 0 = Refl

export
largeHalfGrowsEvery2 : (n: Nat) -> (largeHalf (S (S n)) = S (largeHalf n))
largeHalfGrowsEvery2 n with (half n)
    largeHalfGrowsEvery2 _ | HalfOdd j = Refl
    largeHalfGrowsEvery2 _ | HalfEven (S j) = Refl
    largeHalfGrowsEvery2 _ | HalfEven 0 = Refl

namespace Prop
    public export
    data Prop: (a: Type) -> (a -> Type) -> Type where
        (#): (f: a) -> (0 prf: p f) -> Prop a p

public export
(#) : (a: Type) -> (a-> Type) -> Type
(#) a f = Prop a f

public export
subject : a # p -> a
subject (f # prf) = f

namespace LProp
    public export
    data LProp: (a: Type) -> (a -> Type) -> Type where
        (##): (1 f: a) -> (0 prf: p f) -> LProp a p

infixr 4 ##

public export
(##) : (a: Type) -> (a-> Type) -> Type
(##) a f = LProp a f

public export
lsubject : a ## p -> a
lsubject (f ## prf) = f
