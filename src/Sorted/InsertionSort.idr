module Sorted.InsertionSort

import Control.Order
import Control.Relation
import Decidable.Equality

import Sorted.IsSortingOf
import Sorted.IsPermutationOf
import Sorted.Sorted
import Sorted.Prop
import Sorted.Relates

%default total

%hide Prelude.(::)
%hide Prelude.Nil
%hide Stream.(::)

0 swapIsPermutation : {x,y: a} -> DecEq a => Container a c => (e: a) -> e .#. (Container.(::) {c} x (Container.(::) y Container.Nil)) = e .#. (Container.(::) {c} y (Container.(::) x Container.Nil))
swapIsPermutation e with (decEq e x, decEq e y)
  swapIsPermutation e | ((Yes Refl), Yes Refl) = Refl
  swapIsPermutation e | ((Yes Refl), No eNEqY) = sym ((cong S $ ConsKeepsRest {c} y [] e eNEqY) `transitive` (ConsAddsOne {c} e [y])) `transitive` (ConsAddsOne {c} e [] `transitive` (ConsKeepsRest {c} y [e] e eNEqY))
  swapIsPermutation e | ((No eNEqX), Yes Refl) = sym (ConsKeepsRest {c} x [e] e eNEqX) `transitive` ((sym (ConsAddsOne {c} e []) `transitive` (cong S (ConsKeepsRest {c} x [] e eNEqX))) `transitive` ConsAddsOne {c} e [x])
  swapIsPermutation e | ((No eNEqX), No eNEqY) = sym ((sym $ NilIsEmpty {c} e) `transitive` (ConsKeepsRest {c} y [] e eNEqY `transitive` (ConsKeepsRest {c} x [y] e eNEqX))) `transitive` ((sym (NilIsEmpty {c} e) `transitive` (ConsKeepsRest {c} x [] e eNEqX)) `transitive` ConsKeepsRest {c} y [x] e eNEqY)

covering
public export
insert : (x: a) -> LinearOrder a rel => Container a c => (xs: (c a) # (IsSortingOf {c} {rel} orig)) -> DecEq a => (c a) # (IsSortingOf {c} {rel} (x::orig))
insert x (f # prf) with (Match f)
  insert x (f # prf) | (Left fIsNil) = [x] # (Singleton x, x :: replace {p = IsPermutationOf {c} orig} fIsNil (snd prf))
  insert x (f # prf) | (Right ((y, xs) # yxsEqF)) with (decEq x y)
    insert x (f # prf) | (Right ((x, xs) # yxsEqF)) | (Yes Refl) = (x::x::xs) # case (yxsEqF, prf) of (Refl, sXXs, pXXs) => (reflexive :@: sXXs, x :: pXXs)
    insert x (f # prf) | (Right ((y, xs) # yxsEqF)) | (No xNEqY) with (connex {rel} xNEqY)
      insert x (f # prf) | (Right ((y, xs) # yxsEqF)) | (No xNEqY) | (Left relXY) = (x::y::xs) # case (yxsEqF, prf) of (Refl, sXXs, pYXs) => (relXY :@: sXXs, x :: pYXs)
      insert x (f # prf) | (Right ((y, xs) # yxsEqF)) | (No xNEqY) | (Right relYX) =
        let
            xs' # step = insert {rel} {orig=xs} x (xs # (tail $ fst prf, reflexive @{reflexiveIsPermutationOf}))
        in (y::xs') #
          case (yxsEqF, prf, step) of
            (Refl, (sYXs, pYXs), sXs', pXs') =>
              let
                choo = Ipo (swapIsPermutation {x} {y}) ++ reflexive @{reflexiveIsPermutationOf} {x=xs}
                floo = ConcMerges
                sol = (((x :: pYXs) `transitive` (?help)) @{transitiveIsPermutationOf} `transitive` ?i_0) @{transitiveIsPermutationOf}
              in (((relYX :: head sYXs) {rel} -@-> pXs') {rel} :: sXs', sol)
      --       let
      --           (xs'sorted, xs'perm) = step
      --           (f_sorted, f_perm) = prf
      --           std : Sorted {rel} (y::xs') = ((relYX :: head f_sorted) {rel} -@-> xs'perm) {rel} :: xs'sorted
      --           -- ((((x :: yxs'perm) `transitive` (Ipo (swapIsPermutation {c} {x} {y}) ++ reflexive @{reflexiveIsPermutationOf} {x=xs})) @{transitiveIsPermutationOf}) `transitive` 
      --           ipo = Ipo (swapIsPermutation {c} {x} {y})
      --           yxs'perm = (y :: xs'perm)
      --           prm : IsPermutationOf {c} (x::orig) (y::xs') = ?i_0
      --       in (std, prm)


--     insert x ((y :: xs) # prf) | (No xNEqY) | (Right relYX) =
--         let
--             xs' # step = insert {rel=rel} {orig=xs} x (xs # (tail $ fst prf, reflexive @{reflexiveIsPermutationOf}))
--         in (y::xs') #
--             let
--                 (xs'sorted, xs'perm) = step
--                 (yxs_sorted, yxs'perm) = prf
--             in (
--                 ((relYX :: head yxs_sorted) {rel=rel} -@-> xs'perm) {rel=rel} :: xs'sorted,
--                 ((((x :: yxs'perm) `transitive` (Ipo (swapIsPermutation {x} {y}) ++ reflexive @{reflexiveIsPermutationOf} {x=xs})) @{transitiveIsPermutationOf}) `transitive` )

covering
public export
insertionSort : (as: c a) ->  DecEq a => (lo: LinearOrder a rel) => (ct: Container a c) => (c a) # (IsSortingOf @{lo} as)
-- insertionSort [] = [] # (Nil, reflexive @{reflexiveIsPermutationOf})
-- insertionSort (x::xs) = insert x $ insertionSort xs
