module Sorted.Occurs

import Decidable.Equality

%default total

||| A proof that some element occurs in a list n number of times.
public export
data Occurs : a -> Nat -> List a -> Type where
    ||| A proof that the element is at the head of the list
    Here : Occurs occurrent occurrencies occurrences ->  Occurs occurrent (1+occurrencies) (occurrent :: occurrences)
    ||| A proof that the element is in the tail of the list
    There : Occurs occurrent occurrencies occurrences -> Not (occurrent=notTheOccurrent) -> Occurs occurrent occurrencies (notTheOccurrent :: occurrences)
    ||| A proof that the element is not in the empty list
    Nowhere: Occurs occurrent 0 []

public export
OccursTheSameNumberOfTimes : Occurs x m xs -> Occurs x n xs -> m = n
OccursTheSameNumberOfTimes Nowhere Nowhere = Refl
OccursTheSameNumberOfTimes (There _ f) (Here _) = void $ f Refl
OccursTheSameNumberOfTimes (There y _) (There z _) = OccursTheSameNumberOfTimes y z
OccursTheSameNumberOfTimes (Here _) Nowhere impossible
OccursTheSameNumberOfTimes (Here pm) (Here pn) = cong S $ OccursTheSameNumberOfTimes pm pn
OccursTheSameNumberOfTimes (Here _) (There _ f) = void $ f Refl

public export
[uninhabitedOccursAtLeastOnceInNil] Uninhabited (Occurs x (S _) []) where
  uninhabited Here impossible

public export
[uninhabitedOccursZeroTimesWhenHeadMatches] Uninhabited (Occurs x 0 (x::xs)) where
  uninhabited (There _ f) = f Refl

public export
countOccurrences: DecEq a => (x: a) -> (l: List a) -> DPair Nat (\n => Occurs x n l)
countOccurrences x [] = (0 ** Nowhere)
countOccurrences x (y :: xs) with (countOccurrences x xs)
  countOccurrences x (y :: xs) | (f ** prf) with (decEq x y)
    countOccurrences x (y :: xs) | (f ** prf) | (Yes z) = (S f ** rewrite sym z in Here prf)
    countOccurrences x (y :: xs) | (f ** prf) | (No contra) = (f ** There prf contra)

public export
(::) : (x: a) -> Occurs x n xs -> Occurs x (S n) (x::xs)
(::) _ y = Here y

public export
tail : Occurs x (S n) (x::xs) -> Occurs x n xs
tail (Here y) = y
tail (There y f) = void $ f Refl

public export
(+) : Occurs x n xs -> Occurs x m ys -> Occurs x (n+m) (xs++ys)
(+) (Here y) z = Here (y + z)
(+) (There y f) z = There (y + z) f
(+) Nowhere z = z
