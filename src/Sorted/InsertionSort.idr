module Sorted.InsertionSort

import Control.Order
import Control.Relation
import Decidable.Equality

import Sorted.IsSortingOf
import Sorted.IsPermutationOf
import Sorted.Sorted
import Sorted.Occurs
import Sorted.Prop
import Sorted.Relates

%default total

swapIsPermutation : Occurs e n [x, y] -> Occurs e n [y, x]
swapIsPermutation (Here Nowhere) impossible
swapIsPermutation (Here (There nw eNEqY)) = There (Here nw) eNEqY
swapIsPermutation (Here (Here nw)) = Here (Here nw)
swapIsPermutation (There (Here nw) eNEqX) = Here (There nw eNEqX)
swapIsPermutation (There (There nw eNEqY) eNEqX) = There (There nw eNEqX) eNEqY

covering
public export
insert : (x: a) -> (lo: LinearOrder a rel) => (xs: (List a) # (IsSortingOf lo orig)) -> DecEq a => (List a) # (IsSortingOf lo (x::orig))
insert x ([] # prf) = [x] # (Singleton, x :: snd prf)
insert x ((y :: xs) # prf) with (decEq x y)
  insert x ((x :: xs) # prf) | (Yes Refl) = (x::x::xs) # (reflexive :@: fst prf, x:: snd prf)
  insert x ((y :: xs) # prf) | (No xNEqY) with (connex {rel=rel} xNEqY)
    insert x ((y :: xs) # prf) | (No xNEqY) | (Left relXY) = (x::y::xs) # (relXY :@: fst prf, x :: snd prf)
    insert x ((y :: xs) # prf) | (No xNEqY) | (Right relYX) =
        let
            xs' # step = insert {rel=rel} {orig=xs} x (xs # (tail $ fst prf, reflexive @{reflexiveIsPermutationOf}))
        in (y::xs') #
            let
                (xs'sorted, xs'perm) = step
                (yxs_sorted, yxs'perm) = prf
            in (
                ((relYX :: head yxs_sorted) {rel=rel} -@-> xs'perm) {rel=rel} :: xs'sorted,
                ((((x :: yxs'perm) `transitive` (Ipo (swapIsPermutation {x} {y}) ++ reflexive @{reflexiveIsPermutationOf} {x=xs})) @{transitiveIsPermutationOf}) `transitive` (y :: xs'perm)) @{transitiveIsPermutationOf})

covering
public export
insertionSort : (as: List a) ->  DecEq a => (lo: LinearOrder a rel) => (List a) # (IsSortingOf lo as)
insertionSort [] = [] # (Nil, reflexive @{reflexiveIsPermutationOf})
insertionSort (x::xs) = insert x $ insertionSort xs
