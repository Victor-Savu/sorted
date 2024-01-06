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

infixr 4 ..=..

||| If an element occurs in a list the same number of times no matter how you count it.
public export
(..=..) : Occurs x m xs -> Occurs x n xs -> m = n
Nowhere ..=.. Nowhere = Refl
(There _ f) ..=.. (Here _) = void $ f Refl
(There y _) ..=.. (There z _) = y ..=.. z
(Here _) ..=.. Nowhere impossible
(Here pm) ..=.. (Here pn) = cong S (pm ..=.. pn)
(Here _) ..=.. (There _ f) = void $ f Refl

public export
[uninhabitedOccursAtLeastOnceInNil] Uninhabited (Occurs x (S _) []) where
  uninhabited Here impossible

public export
[uninhabitedOccursZeroTimesWhenHeadMatches] Uninhabited (Occurs x 0 (x::xs)) where
  uninhabited (There _ f) = f Refl

||| Count the number of times a value occurs in a list.
public export
countOccurrences: DecEq a => (x: a) -> (l: List a) -> DPair Nat (\n => Occurs x n l)
countOccurrences x [] = (0 ** Nowhere)
countOccurrences x (y :: xs) with (countOccurrences x xs)
  countOccurrences x (y :: xs) | (f ** prf) with (decEq x y)
    countOccurrences x (y :: xs) | (f ** prf) | (Yes z) = (S f ** rewrite sym z in Here prf)
    countOccurrences x (y :: xs) | (f ** prf) | (No contra) = (f ** There prf contra)

public export
tail : Occurs x (S n) (x::xs) -> Occurs x n xs
tail (Here y) = y
tail (There _ f) = void $ f Refl

public export
(+) : Occurs x n xs -> Occurs x m ys -> Occurs x (n+m) (xs++ys)
(+) (Here y) z = Here (y + z)
(+) (There y f) z = There (y + z) f
(+) Nowhere z = z
