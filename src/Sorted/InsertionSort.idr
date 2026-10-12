module Sorted.InsertionSort

import Control.Order
import Control.Relation
import Control.WellFounded
import Decidable.Equality
import Data.Nat

import Sorted.IsSortingOf
import Sorted.IsPermutationOf
import Sorted.Sorted
import Sorted.Relates
import Sorted.Sequence

%default total


insertionSort' : LinearOrder a rel => Sequence a c => (xs: c) -> (0 acc: SizeAccessible xs) -> Subset c (IsSortingOf {c} {rel} xs)
insertionSort' xs (Access acc) = case IsNil xs of
  (Yes Refl) => Element xs (Iso [] (Ipo (\0 e => Refl)))
  (No xs≠【】) => (Head xs xs≠【】 :: insertionSort' {rel} (Tail xs xs≠【】) (acc _ (eqLTE $ TailIsShorter xs xs≠【】))) -@-> reflexiveFromEq @{reflexiveIsPermutationOf} (sym $ HeadTail xs xs≠【】)

covering
export
insertionSort : LinearOrder a rel => Sequence a c => (xs: c) ->  Subset c (IsSortingOf {c} {rel} xs)
insertionSort xs = insertionSort' xs (sizeAccessible xs)
