module Sorted.MergeSort

import Control.Order
import Control.Relation
import Control.WellFounded
import Data.Nat

import public Sorted.Container
import public Sorted.IsPermutationOf
import public Sorted.Prop
import public Sorted.Relates
import public Sorted.Sorted
import public Sorted.IsSortingOf

%default total

%hide Prelude.Types.List.(++)
%hide Prelude.Types.SnocList.(++)
%hide Prelude.Types.String.(++)
%hide Prelude.(::)
%hide Prelude.Nil
%hide Stream.(::)

public export
data Split : Container a c => c a -> Type where
    SplitNil : Split @{ct} ([] @{ct})
    SplitOne : (x: a) -> Split @{ct} (Container.(::) @{ct} x (Container.Nil @{ct}))
    SplitPair : (ls: c a) -> (0 _: ls = Container.Nil @{ct} -> Void) -> (rs: c a) -> (0 _: rs = Container.Nil @{ct} -> Void) -> (0 _: (xs ~@~ (Container.(++) @{ct} ls rs)) @{ct}) -> Split @{ct} {c} xs


split' : DecEq a => Container a c => (xs : c a) -> (0 acc: SizeAccessible @{ContainerSized} xs) -> Split xs
split' xs acc with (Match xs)
  split' _ acc | (Left Refl) = SplitNil
  split' xs acc | (Right ((x, txs) # xtxs≈xs)) with (Match txs)
    split' xs acc | (Right ((x, txs) # xtxs≈xs)) | (Left txs≈Nil) =
        replace {p = Split} (replace {p = \q => x :: q = xs} txs≈Nil xtxs≈xs) (SplitOne x)
    split' xs (Access acc) | (Right ((x, txs) # xtxs≈xs)) | (Right ((x', ttxs) # x'ttxs≈txs)) =
        case (split' ttxs (acc _ (LTESucc ((lteSuccRight $ eqLTE Refl) \=> eqLTE (sym SizedCons)) \=> eqLTE (sym SizedCons \=> cong (size @{ContainerSized}) ((cong (x::) x'ttxs≈txs \=> xtxs≈xs)))))) of
            SplitNil => SplitPair [x] (uninhabited @{uninhabitedConsIsNil}) [x'] (uninhabited @{uninhabitedConsIsNil}) (
                replace {p = IsPermutationOf xs}
                  (sym (ConcReduces _ _ _ \=> cong (x::) (ConcNilLeftNeutral _) \=> (replace {p = \q => x :: q = xs} (sym x'ttxs≈txs) xtxs≈xs)))
                  (reflexive @{reflexiveIsPermutationOf}))
            SplitOne x'' =>
                SplitPair [x,x''] (uninhabited @{uninhabitedConsIsNil}) [x'] (uninhabited @{uninhabitedConsIsNil}) (
                  ((replace {p = IsPermutationOf xs} (sym xtxs≈xs \=> cong (x::) (sym x'ttxs≈txs)) (reflexive @{reflexiveIsPermutationOf}) \=>
                    (x :: Ipo swapIsPermutation)) @{transitiveIsPermutationOf} \=>
                      replace {p = IsPermutationOf [x,x'',x']}
                        (cong (x::) (cong (x''::) (sym $ ConcNilLeftNeutral _) \=> sym (ConcReduces _ _ _)) \=> sym (ConcReduces _ _ _))
                        (reflexive @{reflexiveIsPermutationOf})) @{transitiveIsPermutationOf})
            SplitPair ls ls≠Nil rs rs≠Nil p =>
                SplitPair (x::ls) (uninhabited @{uninhabitedConsIsNil}) (x'::rs) (uninhabited @{uninhabitedConsIsNil}) (
                  ((replace {p = IsPermutationOf xs} (sym (cong (x::) x'ttxs≈txs \=> xtxs≈xs)) (reflexive @{reflexiveIsPermutationOf}) \=> x :: x' :: p)  @{transitiveIsPermutationOf} \=>
                    (((pong {p=(x::)} (x::) (symmetric @{symmetricIsPermutationOf} (shiftPermutation $ reflexive @{reflexiveIsPermutationOf}))) \=>
                      replace {p = IsPermutationOf _} (sym $ ConcReduces _ _ _) (reflexive @{reflexiveIsPermutationOf})) @{transitiveIsPermutationOf})) @{transitiveIsPermutationOf})
        

export
split : DecEq a => Container a c => (xs : c a) -> Split xs
split xs = split' xs (sizeAccessible @{ContainerSized} xs)

0 lteSum : LTE a b -> LTE c d -> LTE (a+c) (b+d)
lteSum LTEZero LTEZero = LTEZero
lteSum LTEZero (LTESucc x) = LTESucc (x \=> (lteAddRight _) \=> eqLTE (plusCommutative _ _)) \=> eqLTE (plusSuccRightSucc _ _ )
lteSum (LTESucc x) LTEZero = LTESucc (eqLTE (plusZeroRightNeutral _) \=> x \=> lteAddRight _)
lteSum (LTESucc x) (LTESucc y) = LTESucc (eqLTE (sym $ plusSuccRightSucc _ _) \=> LTESucc (lteSum x y) \=> eqLTE ((plusSuccRightSucc _ _)))

0 atLeastOneInNonEmpty : Container a c => (xs = [] -> Void) -> LTE 1 (size @{ContainerSized {c}} xs)
atLeastOneInNonEmpty xs≠Nil with (Match xs)
  atLeastOneInNonEmpty xs≠Nil | (Left Refl) = void $ xs≠Nil Refl
  atLeastOneInNonEmpty xs≠Nil | (Right ((x, xs') # Refl)) = LTESucc LTEZero \=> eqLTE (sym $ SizedCons)

mergeSort' : DecEq a => LinearOrder a rel => Container a c => (xs: c a) -> (0 acc: SizeAccessible @{ContainerSized} xs) -> (c a) # (IsSortingOf {rel} xs)
mergeSort' xs acc with (split xs)
  mergeSort' _ (Access acc) | SplitNil = [] # []
  mergeSort' _ (Access acc) | SplitOne x = [x] # (Iso (Singleton x) (Ipo (\_ => Refl)))
  mergeSort' xs (Access acc) | SplitPair ls ls≠Nil rs rs≠Nil p =
    let
      left = mergeSort' {rel} ls (acc _ (lteSum (atLeastOneInNonEmpty rs≠Nil) (eqLTE Refl) \=> eqLTE (sym (PermutationHasSameSize p \=> SizedConc _ _ \=> (plusCommutative _ _)))))
      right = mergeSort' {rel} rs (acc _ (lteSum (atLeastOneInNonEmpty ls≠Nil) (eqLTE Refl) \=> eqLTE (sym (PermutationHasSameSize p \=> SizedConc _ _))))
      xs' # iso = left ++ right
    in
      xs' # (iso -@-> p)

||| Sort a list in accordance to the linear order induced by rel.
||| This is an implementation of the merge sort algorithm.
export
mergeSort : DecEq a => LinearOrder a rel => Container a c => (xs: c a) -> (c a) # (IsSortingOf {rel} xs)
mergeSort xs = mergeSort' xs (sizeAccessible @{ContainerSized} xs)

