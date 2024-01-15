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
export
insert : (x: a) -> LinearOrder a rel => Container a c => (xs: (c a) # (IsSortingOf {c} {rel} orig)) -> DecEq a => (c a) # (IsSortingOf {c} {rel} (x::orig))
insert x (f # prf) with (Match f)
  insert x (f # (Iso _ prf)) | (Left fIsNil) = [x] # Iso (Singleton x) (x :: replace {p = IsPermutationOf {c} orig} fIsNil prf)
  insert x (f # prf) | (Right ((y, xs) # yxsEqF)) with (decEq x y)
    insert x (f # prf) | (Right ((x, xs) # yxsEqF)) | (Yes Refl) = (x::x::xs) # case (yxsEqF, prf) of (Refl, Iso sXXs pXXs) => Iso (reflexive :@: sXXs) (x :: pXXs)
    insert x (f # prf) | (Right ((y, xs) # yxsEqF)) | (No xNEqY) with (connex {rel} xNEqY)
      insert x (f # prf) | (Right ((y, xs) # yxsEqF)) | (No xNEqY) | (Left relXY) = (x::y::xs) # case (yxsEqF, prf) of (Refl, Iso sXXs pYXs) => Iso (relXY :@: sXXs) (x :: pYXs)
      insert x (f # prf) | (Right ((y, xs) # yxsEqF)) | (No xNEqY) | (Right relYX) =
        let
            xs' # step = insert {rel} {orig=xs} x (xs # Iso (tail {ys'=f} {ysIsCons=yxsEqF} (let Iso sYXs pYXs = prf in sYXs)) (reflexive @{reflexiveIsPermutationOf}))
        in (y::xs') #
          case (yxsEqF, prf, step) of
            (Refl, Iso sYXs pYXs, Iso sXs' pXs') =>
              let
                oioi = (replace {p = \q => IsPermutationOf (x::y::xs) q}
                  (conLeftCons y $ conLeftCons x $ ConcNilLeftNeutral xs)
                  (replace {p = \q => IsPermutationOf q (((y :: ((x :: (Container.Nil {c})) {c})) {c}) ++ xs)}
                    (conLeftCons x $ conLeftCons y $ ConcNilLeftNeutral xs)
                    (Ipo (swapIsPermutation {x} {y}) ++ reflexive @{reflexiveIsPermutationOf} {x=xs})) `transitive`
                      (y :: pXs')) @{transitiveIsPermutationOf}
                sol = (((x :: pYXs) `transitive` oioi) @{transitiveIsPermutationOf} )
              in Iso (((relYX :: head {ys=f} {ysIsCons=yxsEqF} sYXs) {rel} -@-> pXs') {rel} :: sXs') sol

covering
export
insertionSort : (as: c a) ->  DecEq a => LinearOrder a rel => Container a c => (c a) # (IsSortingOf {c} {rel} as)
insertionSort as with (Match as)
  insertionSort _ | Left Refl = [] # Iso [] (reflexive @{reflexiveIsPermutationOf} {x=([] {c})})
  insertionSort _ | Right ((x, xs) # prf) = rewrite sym prf in insert x $ insertionSort xs
