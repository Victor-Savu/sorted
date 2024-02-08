module Sorted.Container

import public Control.Relation
import public Control.WellFounded
import Data.Void
import Data.Nat
import public Decidable.Equality

import public Sorted.Prop

infixr 9 .#.

%default total

%hide Prelude.(::)
%hide Prelude.Stream.(::)
%hide Prelude.Nil


export
ford : (0 _: a = b) -> a -> b
ford Refl = id

||| A container is a type that
||| a. has an element representing the empty container
||| b. has a way to add an element to an existing container such that the resulting container contains exactly one more instance of that new element
|||    and just as many instances of any other element of the original container
|||
||| The container interface is satisfied by:
||| - the type a representing the type of elements in the container
||| - the type construtor c: Type -> Type which constructs the type of the container: c
||| if it can:
||| 1. provide a counting function (.#.): a -> c -> Nat which counts the number of occurrences of a value of type a in the container of type c
||| 1. produce an "empty" container from thin air (using Nil). The empty container is a specific instance of c (call it xs) which must satisfy the
|||    property that any value of type a occurs 0 times in xs according to the counting function. Basically, a container is empty if nothing occurs in it.
||| 2. produce an "inhabited" container by applying (::) to an element of type a (call it x) and another container of type c (call it xs). The
|||    "inhabited" container is a specific instance of c (call it xxs) which must satisfy two properties:
|||    1. As counted by (.#.), x occurs in xxs one time more than it occurs in xs (showing that x was inserted exactly once by (::))
|||    2. Given any other element of a (call it x'), that element will occur the same number of times in xs as it does in xxs (showing that no other
|||       element of xs was duplicated or removed by (::))
export
interface Container a c | c where
    constructor MkContainer

    (.#.) : a -> c -> Nat

    Nil : c
    0 NilIsEmpty : forall x. x .#. [] = 0
    0 NilIsUnique : forall xs. (forall x. x .#. xs = 0) -> xs = []

    (::) : a -> c -> c
    0 ConsAddsOne : forall x, xs. (1 + x .#. xs) = x .#. (x :: xs)
    0 ConsKeepsRest :forall x, x', xs. (ne: Not (x'=x)) -> x' .#. xs =  x' .#. (x::xs)
    0 ConsBiinjective : Biinjective (::)

    (++) : (xs: c) -> (ys: c) -> c
    0 ConcNilLeftNeutral : forall xs. [] ++ xs = xs
    0 ConcReduces : forall x, xs, ys. (x::xs) ++ ys = x :: (xs ++ ys)
    
    ContainerSized : Sized c
    0 SizedNil: size @{ContainerSized} [] = 0
    0 SizedCons: forall x, xs. size @{ContainerSized} (x::xs) = S (size @{ContainerSized} xs)

    Match : (xs: c) -> Either (xs = []) ((a, c) # \q => (fst q)::(snd q) = xs)


infixl 4 \=>

export
(\=>) : {x, y, z: ty} -> Transitive ty rel => rel x y -> rel y z -> rel x z
a \=> b = transitive a b

export
[uninhabitedConsIsNil] Container a c => Uninhabited (x::xs = ([] {c})) where
    uninhabited xXsIsNil = absurdity $ ConsAddsOne \=> (cong (x .#.) xXsIsNil) \=>  (NilIsEmpty)

export
0 ConcNilRightNeutral : (xs: c) -> DecEq a => Container a c => xs ++ [] = xs
ConcNilRightNeutral xs with (sizeAccessible @{ContainerSized} xs)
  ConcNilRightNeutral xs | acc with (Match xs)
    ConcNilRightNeutral _ | acc | Left Refl = ConcNilLeftNeutral
    ConcNilRightNeutral _ | Access acc | Right ((x, xs') # Refl) = ConcReduces \=> (cong (x ::) (ConcNilRightNeutral xs' | acc _ (rewrite SizedCons {x} {xs=xs'} in reflexive)))

export
eqLTE : {x, y: Nat} -> x = y -> LTE x y
eqLTE Refl = reflexive

export
0 ConcMerges : (xs: c) -> (ys: c) -> (x: a) -> DecEq a => Container a c => x .#. (xs ++ ys) = x .#. xs + x .#. ys
ConcMerges xs ys x with (sizeAccessible @{ContainerSized} xs)
  ConcMerges xs ys x |acc with (Match xs)
    ConcMerges _ ys x | acc | (Left Refl) = cong2 (+) (sym NilIsEmpty) (cong (x .#.) $ ConcNilLeftNeutral)
    ConcMerges _ ys x | acc | (Right ((x', xs') # Refl)) with (decEq x x')
      ConcMerges _ ys x | Access acc | (Right ((x, xs') # Refl)) | (Yes Refl) = (((cong (x .#.) ConcReduces) \=> sym ConsAddsOne) \=> (cong S (ConcMerges xs' ys x | acc _ (rewrite SizedCons {x} {xs=xs'} in reflexive)))) \=> (cong (+ (x .#. ys)) ConsAddsOne)
      ConcMerges _ ys x | Access acc | (Right ((x', xs') # Refl)) | (No x≠x') = (((cong (x .#.) ConcReduces) \=> (sym $ ConsKeepsRest x≠x')) \=> (ConcMerges xs' ys x | acc _ (rewrite SizedCons {x=x'} {xs=xs'} in reflexive))) \=> (cong (+ (x .#. ys)) $ ConsKeepsRest x≠x')

export
0 SizedConc : Container a c => (xs, ys: c) -> size @{ContainerSized} (xs ++ ys) = size @{ContainerSized} xs + size @{ContainerSized} ys
SizedConc xs ys with (sizeAccessible @{ContainerSized} xs)
  SizedConc xs ys | acc with (Match xs)
    SizedConc _ ys | acc | (Left Refl) = cong (size @{ContainerSized}) ConcNilLeftNeutral \=> replace {p = \q => (size @{ContainerSized} ys = q + size @{ContainerSized} ys)} (sym $ SizedNil {c}) reflexive
    SizedConc _ ys | Access acc | (Right ((x, xs') # Refl)) = cong (size @{ContainerSized}) ConcReduces \=> SizedCons \=>
        (cong S (SizedConc xs' ys | acc _ $ eqLTE $ sym $ SizedCons {c})) \=> (cong (+ size @{ContainerSized} ys) (sym $ SizedCons {x} {xs=xs'}))

export
yes : DecEq a => (x: a) -> decEq x x = Yes Refl
yes x with (decEq x x)
  yes x | (Yes Refl) = Refl
  yes x | (No xNEqX) = void $ xNEqX Refl

export
no : DecEq a => {x, x': a} -> (x≠x': Not (x=x')) -> Not (x=x') # (\ctra => decEq x x' = No {prop=(x=x')} ctra)
no x≠x' with (decEq x x')
  no x'NEqX' | (Yes Refl) = void $ x'NEqX' Refl
  no _ | (No x≠x') = x≠x' # Refl

export
0 Next : {x: a} -> {xs: c} -> Container a c => {n: Nat} -> x .#. xs = n -> x .#. (Container.(::) x xs) = 1+n
Next prf = sym ConsAddsOne \=> (cong S prf)

export
0 conLeftCons : Container a c => (x: a) -> {0 xs, ys, zs: c} -> xs ++ ys = zs -> (x::xs) ++ ys = x::zs
conLeftCons x prf = ConcReduces \=> (cong (x::) prf)

export
0 findFirst : DecEq a => Container a c => (x: a) -> (xs: c) -> Either (x .#. xs = 0) ((c, c) # (\(l, r) => (x .#. l = 0, l ++ x::r = xs)))
findFirst x xs with (sizeAccessible @{ContainerSized} xs)
  findFirst x xxs | acc with (Match xxs)
    findFirst x _ | acc | (Left Refl) = Left (NilIsEmpty)
    findFirst x _ | acc | (Right ((x', xs) # Refl)) with (decEq x x')
      findFirst x _ | acc | (Right ((_, xs) # Refl)) | (Yes Refl) = Right (([], xs) # (NilIsEmpty, ConcNilLeftNeutral))
      findFirst x _ | Access acc | (Right ((x', xs) # Refl)) | (No x≠x') =
        case (findFirst x xs | acc _ (replace {p = LTE (S (size @{ContainerSized} xs))} (sym $ SizedCons) reflexive)) of
          (Left x∉xs) => Left ((sym $ ConsKeepsRest x≠x') \=> x∉xs)
          (Right ((l, r) # (x∉l, Refl))) =>
            Right ((x'::l, r) # ((sym $ ConsKeepsRest x≠x') \=> x∉l, ConcReduces))
