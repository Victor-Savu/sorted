module Sorted.MergeSort

import Control.Order
import Control.Relation
import Control.WellFounded
import Data.Nat

import public Sorted.Container
import public Sorted.IsPermutationOf
import public Sorted.Relates
import public Sorted.Sorted
import public Sorted.IsSortingOf
import Sorted.Sequence

%default total

%hide Prelude.Types.List.(++)
%hide Prelude.Types.SnocList.(++)
%hide Prelude.Types.String.(++)
%hide Prelude.(::)
%hide Prelude.Nil
%hide Stream.(::)



namespace Split

  public export
  data Either0: Type -> Type -> Type where
     Left0: (0 _: a) -> Either0 a b
     Right0: (0 _: b) -> Either0 a b

  public export
  record Split {auto 0 ct: Container a c} (xs: c)  where
    constructor MkSplit
    left: c
    right: c
    0 left⧺right≎xs: left++right ~@~ xs
    ⋕⎨left⎬≅⋕⎨right⎬: Either0 (size left = size right) (S(size left) = size right)
  

unzipper' : DecEq a => Container a c => (xs : c) -> (0 acc: SizeAccessible xs) -> Split xs
unzipper' xs (Access acc) = case IsNil xs  of
  (Yes Refl) => MkSplit [] [] ConcNilRightNeutral (Left0 Refl)
  (No xs≠【】) =>
    let
      rec = unzipper' (Tail xs xs≠【】) (acc _ (eqLTE $ TailIsShorter _ _))
    in
      case rec.⋕⎨left⎬≅⋕⎨right⎬ of
        (Left0 the⋕⎨left⎬≗⋕⎨right⎬) =>
          MkSplit
            rec.left
            (Head xs xs≠【】 :: rec.right)
            ((shiftPermutation (reflexive @{reflexiveIsPermutationOf}) \=> (((Head xs xs≠【】 :: rec.left⧺right≎xs) \=> (reflexiveFromEq @{reflexiveIsPermutationOf} (HeadTail xs xs≠【】))) @{transitiveIsPermutationOf})) @{transitiveIsPermutationOf})
            $ Right0 $ cong S the⋕⎨left⎬≗⋕⎨right⎬ \=> sym ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬
        (Right0 s⋕⎨left⎬≗⋕⎨right⎬) =>
          MkSplit
            (Head xs xs≠【】 :: rec.left)
            rec.right
            (
              let
                l0 = (Head xs xs≠【】 ::  rec.left⧺right≎xs \=> (reflexiveFromEq @{reflexiveIsPermutationOf} (HeadTail xs xs≠【】))) @{transitiveIsPermutationOf}
              in (shiftPermutationLeft (reflexive @{reflexiveIsPermutationOf}) \=> (l0)) @{transitiveIsPermutationOf}
            )
            $ Left0 $ (∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬ \=> s⋕⎨left⎬≗⋕⎨right⎬)

export
unzipper : DecEq a => Container a c => (xs : c) -> Split xs
unzipper xs = unzipper' xs (sizeAccessible xs)

0 atLeastOneInNonEmpty : Container a c => Not (x∷xs = ([] {c})) -> LTE 1 (size x∷xs)
atLeastOneInNonEmpty x∷xs≠【】 =
  let
    ⋕⎨x∷xs⎬≐S⋕⎨xs⎬ = (sym $ cong size (HeadTail x∷xs x∷xs≠【】)) \=> ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬
  in rewrite ⋕⎨x∷xs⎬≐S⋕⎨xs⎬ in LTESucc LTEZero

mergeSort' : DecEq a => LinearOrder a rel => Sequence a c => (xs: c) -> (0 acc: SizeAccessible xs) -> Subset (c) (IsSortingOf {rel} xs)
mergeSort' xs (Access acc) =
  let
    split = unzipper xs
  in case split.⋕⎨left⎬≅⋕⎨right⎬ of
    (Left0 the⋕⎨left⎬≗⋕⎨right⎬) => case IsNil split.right of
      (Yes right≗【】) => Element [] (Iso [] (((symmetric @{symmetricIsPermutationOf} split.left⧺right≎xs \=> (reflexiveFromEq @{reflexiveIsPermutationOf} (∀xs‥⋕⎨xs⎬≐0⇒xs≐【】 (the⋕⎨left⎬≗⋕⎨right⎬ \=> cong size right≗【】 \=> ⋕⎨【】⎬≐0)) ++ reflexiveFromEq @{reflexiveIsPermutationOf} right≗【】)) @{transitiveIsPermutationOf} \=> ConcNilRightNeutral) @{transitiveIsPermutationOf}))
      (No right≠【】) =>
        let
          rnz = sym ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬ \=> cong size (HeadTail split.right right≠【】)
          lnz = rnz \=> sym the⋕⎨left⎬≗⋕⎨right⎬
          pss = sym ConcAddsSizes \=> PermutationHasSameSize split.left⧺right≎xs
        in 
          mergeSort' split.left (acc _ (LTESucc (lteAddRight _) \=> eqLTE (plusSuccRightSucc _ _ \=> cong (size split.left +) rnz \=> pss)))
          ++ mergeSort' split.right (acc _ (lteAddRight _ \=> eqLTE (plusCommutative _ _) \=> eqLTE ((sym $ plusSuccRightSucc _ _) \=> cong (+ size split.right) lnz \=> pss))) -@-> symmetric @{symmetricIsPermutationOf} split.left⧺right≎xs
    (Right0 s⋕⎨left⎬≗⋕⎨right⎬) =>
      let
        0 right≠【】: Not (split.right = []) = SizeMeansNotEmpty {xs = split.right} $ sym s⋕⎨left⎬≗⋕⎨right⎬
        0 l0 = (sym $ PermutationHasSameSize split.left⧺right≎xs) \=> ConcAddsSizes \=> sym (plusSuccRightSucc _ _ \=> cong (size split.left +) s⋕⎨left⎬≗⋕⎨right⎬)
        0 xs≠【】 = SizeMeansNotEmpty l0
      in case IsNil split.left of
        (Yes left≗【】) =>
          let
            0 l1 = cong size left≗【】 \=> ⋕⎨【】⎬≐0
            0 tail_xs≗【】 = ∀xs‥⋕⎨xs⎬≐0⇒xs≐【】 $ injective (sym ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬ \=> cong size (HeadTail xs xs≠【】) \=> l0 \=> cong S (cong2 (+) l1 l1))
          in Element [Head xs xs≠【】] (Iso (Singleton (Head xs xs≠【】)) $ JustTheHead xs xs≠【】 tail_xs≗【】)
        (No left≠【】) =>
          let
            0 l2 = lteAddLeft (S (size split.right)) _ _ $ eqLTE (plusCommutative _ _ \=> sym (plusSuccRightSucc _ _) \=> cong (+ size split.right) (sym ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬ \=> cong size (HeadTail split.left left≠【】)) \=> sym ConcAddsSizes \=> PermutationHasSameSize split.left⧺right≎xs)
          in mergeSort' split.left (acc _ (lteAddLeft _ _ _ $ eqLTE (sym l0))) ++ mergeSort' split.right (acc _ l2) -@-> symmetric @{symmetricIsPermutationOf} split.left⧺right≎xs

||| Sort a list in accordance to the linear order induced by rel.
||| This is an implementation of the merge sort algorithm.
export
mergeSort : LinearOrder a rel => Sequence a c => (xs: c) -> Subset (c) (IsSortingOf {rel} xs)
mergeSort xs = mergeSort' xs (sizeAccessible xs)

