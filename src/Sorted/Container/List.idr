module Sorted.Container.List

import Control.Function
import Control.WellFounded
import Data.Void
import Data.List
import Data.Nat
import Decidable.Equality

import Sorted.Sequence

import public Sorted.Container

%default total

public export
DecEq a =>  Container a (List a) where

  x .#. [] = 0
  x .#. (x' :: xs) with (decEq x x')
      x .#. (x :: xs) | (Yes Refl) = 1 + x .#. xs
      x .#. (x' :: xs) | (No _) = x .#. xs

  Nil = []

  IsNil [] = Yes Refl
  IsNil (x :: xs) = No (\x∷xs≐【】 => absurd x∷xs≐【】)

  ∀x‥x⋕【】≐0 = Refl

  x :: y = x :: y

  ConsAddsOne = rewrite decEqSelfIsYes {x} in Refl
  ConsKeepsRest x'≠x = rewrite (decEqContraIsNo x'≠x).snd in Refl

  Head [] x∷xs≠【】 = void $ x∷xs≠【】 Refl
  Head (x :: xs) x∷xs≠【】 = x

  Tail [] x∷xs≠【】 = void $ x∷xs≠【】 Refl
  Tail (x :: xs) x∷xs≠【】 = xs

  HeadTail [] x∷xs≠【】 = void $ x∷xs≠【】 Refl
  HeadTail (x :: xs) x∷xs≠【】 = Refl

  xs ++ ys = xs ++ ys

  ConcAddsCounts =
    let
      0 ans: (x .#. (Prelude.List.(++) xs ys) = plus (x .#. xs) (x .#. ys)) =
        case xs of
          [] => Refl
          (x' :: xs) => case ys of
            [] => rewrite appendNilRightNeutral xs in (Refl \=> sym (plusZeroRightNeutral _))
            (y' :: ys) => case decEq x x' of
              (Yes Refl) => rewrite decEqSelfIsYes {x} in cong S (ConcAddsCounts {c=List a})
              (No x≠x') => rewrite (decEqContraIsNo x≠x').snd in (ConcAddsCounts {c=List a})
    in rewrite ans in Refl

  ContainerSized = MkSized length

  ⋕⎨【】⎬≐0 = Refl

  ∀x‥∀xs‥⋕⎨x∷xs⎬≐S⋕⎨xs⎬ = Refl

  ∀xs‥⋕⎨xs⎬≐0⇒xs≐【】 the⋕⎨x∷xs⎬≐0 =
    let
      0 ans: (xs = []) =
        case xs of
          [] => Refl
          (x :: ys) => absurdity the⋕⎨x∷xs⎬≐0
    in rewrite ans in Refl

DecEq a => OutputSequence a (List a) where
  OutSequenceHead x∷xs x∷xs≠【】 x∷xs≠【】'=
    let
      0 ans: (Head x∷xs x∷xs≠【】 = Head x∷xs x∷xs≠【】') = case x∷xs of
        [] => void $ x∷xs≠【】 Refl
        (x :: xs) => Refl
    in
      rewrite ans in Refl

  OutSequenceTail x∷xs x∷xs≠【】 x∷xs≠【】' =
    let
      0 ans: (Tail x∷xs x∷xs≠【】 = Tail x∷xs x∷xs≠【】') = case x∷xs of
        [] => void $ x∷xs≠【】 Refl
        (x :: xs) => Refl
    in
      rewrite ans in Refl

DecEq a => Sequence a (List a) where
  InSequenceHead x xs = Refl
  InSequenceTail x xs = Refl


-- image': DecEq a => Container a c => (xs: c) -> SizeAccessible @{ContainerSized} xs -> List a
-- image' xs (Access acc) = case IsNil xs of
--   (Yes Refl) => []
--   (No xs≠【】) =>
--     let 
--       res = image' (Tail xs xs≠【】) (acc _ (eqLTE $ TailIsShorter _ xs≠【】))
--     in case (Head xs xs≠【】) .#. (Tail xs xs≠【】) of
--       0 => (Head xs xs≠【】) :: res
--       (S _) => res

-- elementInImage': DecEq a => Container a c => (xs: c) -> SizeAccessible @{ContainerSized} xs -> (x: a) -> x .#. xs = S n -> x .#. image' xs (sizeAccessible @{ContainerSized} xs) = 1
-- elementInImage' xs (Access acc) x x⋕xs≐1∔n =
--     case IsNil xs of
--       (Yes Refl) => void $ SIsNotZ (sym x⋕xs≐1∔n \=> ∀x‥x⋕【】≐0)
--       (No xs≠【】) => case (Head xs xs≠【】) .#. (Tail xs xs≠【】) of
--         0 => rewrite sym $ HeadTail xs xs≠【】 in  case decEq x (Head xs xs≠【】)  of
--           (Yes Refl) => ?e_3
--           (No contra) => ?e_4
--         (S _) => ?e_2
      
      -- let
      --     Access acc = acc
      --     rec = image' (Tail xs xs≠【】) (acc _ (eqLTE $ TailIsShorter _ xs≠【】))
      --   in case (Head xs xs≠【】) .#. rec of
      --     0 => case decEq x (Head xs xs≠【】) of
      --       (Yes Refl) => ?e_5
      --       (No contra) => ?e_3
      --     (S _) => ?e_2

            -- let
            --   l0: (x = Head xs xs≠【】) = ?l0_p
            --   l1: ((.#.) {c=List a} (Head xs xs≠【】) (Head xs xs≠【】 :: rec) = 1) = ?l1_p
            --   -- l2 = cong (x .#. {c=List a}) ?l2_p \=> cong (.#. {c=List a} (Head xs xs≠【】 :: rec)) l0 
            --   l3: (x .#. (Head xs xs≠【】 :: rec) {c=List a} = Head xs xs≠【】 .#. (Head xs xs≠【】 :: rec) {c=List a}) = cong (.#. (Head xs xs≠【】 :: rec) {c=List a}) l0
            --   l4 = cong ((.#.) x {c=List a}) ?l4_p \=> case decEq x (Head xs xs≠【】) of
            --     (Yes Refl) => l3 \=> l1
            --     (No contra) => ?l4_p_2
            -- in ?e_0

-- strangerNotInImage': DecEq a => Container a c => (xs: c) -> SizeAccessible @{ContainerSized} xs -> (x: a) -> x .#. xs = 0 -> x .#. image' xs (sizeAccessible @{ContainerSized} xs) = 0
-- strangerNotInImage' xs acc x x⋕xs≐0 = ?strangerNotInImage'_rhs

  -- case IsNil xs of
  --   (Yes Refl) => void $ SIsNotZ (sym x∈xs \=> ∀x‥x⋕【】≐0)
  --   (No xs≠【】) => let
  -- case IsNil xs of
  --   (Yes Refl) => void $ SIsNotZ (sym x∈xs \=> ∀x‥x⋕【】≐0)
  --   (No xs≠【】) => let
  --       -- l0: (
  --       --     case IsNil xs of
  --       --       Yes Refl => []
  --       --       No xs≠【】 =>
  --       --         let
  --       --           Access acc = sizeAccessible xs
  --       --           rec = image' (Tail xs xs≠【】) (acc (Tail xs xs≠【】) (eqLTE (TailIsShorter xs xs≠【】)))
  --       --         in case Head xs xs≠【】 .#. rec of
  --       --           0 => Head xs xs≠【】 :: rec
  --       --           S _ => rec
  --       --     ) = ?l0_p
  --     in ?l1_0

-- export
-- DecEq a => Container a c => ContainerImage a c (List a) where
--   image xs = image' xs (sizeAccessible @{ContainerSized} xs)
    
--   elementInImage xs = elementInImage' xs (sizeAccessible @{ContainerSized} xs)

--   strangerNotInImage xs = strangerNotInImage' xs (sizeAccessible @{ContainerSized} xs)
