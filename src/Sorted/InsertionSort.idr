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

covering
export
insertionSort : (as: c) ->  DecEq a => LinearOrder a rel => Container a c => c # (IsSortingOf {c} {rel} as)
insertionSort as with (Match as)
  insertionSort _ | Left Refl = [] # Iso [] (reflexive @{reflexiveIsPermutationOf} {x=([] {c})})
  insertionSort _ | Right ((x, xs) # prf) = rewrite sym prf in x :: insertionSort xs
