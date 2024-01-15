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
                leftside = conLeftCons x $ conLeftCons y $ ConcNilLeftNeutral xs
                rightside = conLeftCons y $ conLeftCons x $ ConcNilLeftNeutral xs
                rsc = replace {p = \q => IsPermutationOf (x::y::xs) q} rightside (replace {p = \q => IsPermutationOf q (((y :: ((x :: (Container.Nil {c})) {c})) {c}) ++ xs)} leftside choo)
                oioi: IsPermutationOf (x :: (y :: xs)) (y :: xs') = (rsc `transitive` (y :: pXs')) @{transitiveIsPermutationOf}
                sol = (((x :: pYXs) `transitive` oioi) @{transitiveIsPermutationOf} )
              in (((relYX :: head sYXs) {rel} -@-> pXs') {rel} :: sXs', sol)

covering
public export
insertionSort : (as: c a) ->  DecEq a => LinearOrder a rel => Container a c => (c a) # (IsSortingOf {c} {rel} as)
insertionSort as with (Match as)
  insertionSort _ | Left Refl = [] # (Nil, reflexive @{reflexiveIsPermutationOf})
  insertionSort _ | Right ((x, xs) # prf) = rewrite sym prf in insert x $ insertionSort xs
