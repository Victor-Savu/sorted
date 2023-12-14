module Borrow

import public Sorted.Prop

-- Decidable.Equality

namespace Return
    public export
    data Return: (0 a: Type) -> (b: Type) -> Type where
        (#) : (1 x: a) -> b -> Return a b

-- This is the type of computations that mutably borrow a linear value
-- of type a because the returned linear value of type a may be different
-- from the one that was borrowed.
BorrowMut : Type -> Type -> Type
BorrowMut a b = (1 x: a) -> Return a b

-- This is the type of computations that immutably borrow a linear value
-- of type a because the returned linear value is equal to the one that was
-- borrowed, as proven by the equality property.
Borrow : Type -> Type -> Type
Borrow a b = (1 x: a) -> Return (a ## \y => y = x) b

mut_next_learn_pred : BorrowMut Nat (Maybe Nat)
mut_next_learn_pred 0 = 1 # Nothing
mut_next_learn_pred (S k) = case mut_next_learn_pred k of
    nk # Nothing => (S nk) # (Just 0) 
    nk # (Just pk) => (S nk) # (Just (S pk))
