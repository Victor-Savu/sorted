module Data.Heap

-- import Algebra.Solver.Semiring
import Control.Order
import Control.Relation
import Data.Fin
import Data.List.Views
import Data.Nat
import Data.Void
import Syntax.PreorderReasoning

import Sorted.IsPermutationOf
import Sorted.IsSortingOf
import Sorted.Relates
import Sorted.Sorted

%default total

||| Everything is decidably equal to itself
export
connexRelIsLeft : Connex a rel => Antisymmetric a rel => {x, y : a} -> (x≠y: Not (x = y)) -> (x≤y: rel x y) -> (x≤'y: rel x y ** connex x≠y = Left x≤'y)
connexRelIsLeft x≠y x≤y with (connex {rel} x≠y)
  connexRelIsLeft x≠y x≤y | (Left x≤'y) = (x≤'y ** Refl)
  connexRelIsLeft x≠y x≤y | (Right y≤x) = void $ x≠y (antisymmetric {rel} x≤y y≤x)

||| If you have a proof of inequality, you're sure that `decEq` would give a `No`.
export
connexRelIsRight : Connex a rel => Antisymmetric a rel => {x, y : a} -> (x≠y: Not (x = y)) -> (y≤x: rel y x) -> (y≤'x: rel y x ** connex x≠y = Right y≤'x)
connexRelIsRight x≠y y≤x with (connex {rel} x≠y)
  connexRelIsRight x≠y y≤x | (Left x≤y) = void $ x≠y (antisymmetric {rel} x≤y y≤x)
  connexRelIsRight x≠y y≤x | (Right y≤'x) = (y≤'x ** Refl)

connexIsEither : Connex a rel => Antisymmetric a rel => {x, y : a} -> (x≠y: Not (x = y)) -> Either (x≤'y: rel x y ** connex x≠y = Left x≤'y) (y≤'x: rel y x ** connex x≠y = Right y≤'x)
connexIsEither x≠y with (connex {rel} x≠y)
  connexIsEither x≠y | (Left x≤y) = Left (x≤y ** Refl)
  connexIsEither x≠y | (Right y≤x ) = Right (y≤x ** Refl)

export
Maybe' : Nat -> Type -> Type
Maybe' 0 _ = ()
Maybe' (S _) ty = ty

MkMaybe: (n: Nat) -> Lazy a -> Maybe' n a
MkMaybe 0 _ = ()
MkMaybe (S _) x = x

public export
data Heap : LinearOrder a rel => (n: Nat) -> (h: Maybe' n a) -> Type where
    Nil : Heap @{lo} 0 ()
    Singleton: (h: a) -> Heap @{lo} {a} 1 h
    Prick : (h: a) -> (s: a) -> (0 h≤s: rel h s) -> Heap @{lo} {rel} 2 h
    Balanced : (h: a) -> (0 h≤l: rel h l) -> (0 h≤r: rel h r) -> (left: Heap @{lo} (1+m) l) -> (right: Heap @{lo} (1+m) r) -> Heap @{lo} {rel} (1+(((1+m)+(1+m)))) h
    Imbalanced : (h: a) -> (0 h≤l: rel h l) -> (0 h≤r: rel h r) -> (left: Heap @{lo} (2 + m) l) -> (right: Heap @{lo} (1+m) r) -> Heap @{lo} {rel} (1+(((2+m)+(1+m)))) h

public export
length : LinearOrder a rel => Heap {rel} n h -> Nat
length [] = 0
length (Singleton h) = 1
length (Prick h s h≤s) = 2
length (Balanced h h≤l h≤r left right) = 1 + 2 * length right
length (Imbalanced h h≤l h≤r left right) = 2 + 2 * length right

public export
LinearOrder a rel => Sized (Heap {rel} n h) where
  size = length

public export
ActualMin :  DecEq a => LinearOrder a rel => a -> a -> a
ActualMin x y = case decEq x y of
  Yes Refl => x
  No x≠y => case connex {rel} x≠y of
    Left x≤y => x
    Right y≤x => y


public export
min' : DecEq a => LinearOrder a rel => {n: Nat} -> a -> Maybe' n a -> a
min' {n = 0} x _ = x
min' {n = (S k)} x y = ActualMin {rel} x y


public export
Max' : DecEq a => LinearOrder a rel => a -> a -> a
Max' x y = case decEq x y of
  Yes Refl => x
  No x≠y => case connex {rel} x≠y of
    Left x≤y => y
    Right y≤x => x

public export
min'' : DecEq a => LinearOrder a rel => {m, n: Nat} -> Maybe' m a -> Maybe' n a -> Maybe' (m+n) a
min'' {m = 0} _ x = rewrite plusZeroLeftNeutral n in x
min'' {m = (S k)} x y = min' {rel} x y

public export
smallerLessThanMin : DecEq a => LinearOrder a rel => {h, h', l: a} -> (h≤l: rel h l) -> (h≤h': rel h h') -> rel h (ActualMin {rel} h' l)
smallerLessThanMin h≤l h≤h' = case decEq h' l of
  Yes Refl => rewrite decEqSelfIsYes {x=l} in h≤l
  No h'≠l =>
    let (h'≠l ** decin) = decEqContraIsNo h'≠l in rewrite decin in case connex {rel} h'≠l of
    Left h'≤l => rewrite (connexRelIsLeft h'≠l h'≤l).snd in h≤h'
    Right l≤h' => rewrite (connexRelIsRight h'≠l l≤h').snd in h≤l

public export
minLessThanGreater : DecEq a => LinearOrder a rel => {h, h', l: a} -> (h≤l: rel h l) -> rel (ActualMin {rel} h h') l
minLessThanGreater h≤l = case decEq h h' of
  Yes Refl => rewrite decEqSelfIsYes {x=h} in h≤l
  No h≠h' =>
    let (h≠h' ** decin) = decEqContraIsNo h≠h' in rewrite decin in case connex {rel} h≠h' of
    Left h≤h' => rewrite (connexRelIsLeft h≠h' h≤h').snd in h≤l
    Right h'≤h => rewrite (connexRelIsRight h≠h' h'≤h).snd in (h'≤h \=> h≤l)

public export
minLessThanGreater' : DecEq a => LinearOrder a rel => {h, h', l: a} -> (h≤l: rel h l) -> rel (ActualMin {rel} h' h) l
minLessThanGreater' h≤l = case decEq h' h of
  Yes Refl => rewrite decEqSelfIsYes {x=h} in h≤l
  No h'≠h =>
    let (h'≠h ** decin) = decEqContraIsNo h'≠h in rewrite decin in case connex {rel} h'≠h of
    Left h'≤h => rewrite (connexRelIsLeft h'≠h h'≤h).snd in (h'≤h \=> h≤l)
    Right h≤h' => rewrite (connexRelIsRight h'≠h h≤h').snd in h≤l

public export
congMin : DecEq a => LinearOrder a rel => {h, h', l, l': a} -> (h≤l: rel h l) -> (h'≤l': rel h' l') -> rel (ActualMin {rel} h h') (ActualMin {rel} l l')
congMin h≤l h'≤l' = case decEq h h' of
  Yes Refl => rewrite decEqSelfIsYes {x=h} in smallerLessThanMin {rel} h'≤l' h≤l
  No h≠h' =>
    let (h≠h' ** decin) = decEqContraIsNo h≠h' in rewrite decin in case connex {rel} h≠h' of
    Left h≤h' => rewrite (connexRelIsLeft h≠h' h≤h').snd in smallerLessThanMin {rel} (h≤h' \=> h'≤l') h≤l
    Right h'≤h => rewrite (connexRelIsRight h≠h' h'≤h).snd in smallerLessThanMin {rel} h'≤l' (h'≤h \=> h≤l)

public export
min≤max : DecEq a => LinearOrder a rel => {h, h': a} -> rel (ActualMin {rel} h h') (Max' {rel} h h')
min≤max = case decEq h h' of
  Yes Refl => rewrite decEqSelfIsYes {x=h} in reflexive
  No h≠h' =>
    let (h≠h' ** decin) = decEqContraIsNo h≠h' in rewrite decin in case connex {rel} h≠h' of
    Left h≤h' => rewrite (connexRelIsLeft h≠h' h≤h').snd in h≤h'
    Right h'≤h => rewrite (connexRelIsRight h≠h' h'≤h).snd in h'≤h

public export
minCommutes : DecEq a => LinearOrder a rel => {h, h': a} -> rel (ActualMin {rel} h h') (ActualMin {rel} h' h)
minCommutes = case decEq h h' of
  Yes Refl => rewrite decEqSelfIsYes {x=h'} in reflexive
  No h≠h' => 
    let (h≠h' ** decin) = decEqContraIsNo h≠h' in rewrite decin in case connex {rel} h≠h' of
      Left h≤h' => rewrite (connexRelIsLeft h≠h' h≤h').snd in smallerLessThanMin {rel} reflexive h≤h'
      Right h'≤h => rewrite (connexRelIsRight h≠h' h'≤h).snd in smallerLessThanMin {rel} h'≤h reflexive

public export
minCom : DecEq a => LinearOrder a rel => {x, y: a} -> ActualMin {rel} x y = ActualMin {rel} y x
minCom = case decEq x y of
  Yes Refl => rewrite decEqSelfIsYes {x=y} in Refl
  No x≠y =>
    let (x≠y ** decin) = decEqContraIsNo x≠y in rewrite decin in
    let (y≠x ** decin) = decEqContraIsNo $ negEqSym x≠y in rewrite decin in
    case connex {rel} x≠y of
      (Left x≤y) =>
        let (x≤y ** connex_x≤y) = connexRelIsLeft x≠y x≤y in rewrite connex_x≤y in
        let (x≤y ** connex_x≤y) = connexRelIsRight y≠x x≤y in rewrite connex_x≤y in
        Refl
      (Right y≤x) =>
        let (y≤x ** connex_y≤x) = connexRelIsRight x≠y y≤x in rewrite connex_y≤x in
        let (y≤x ** connex_y≤x) = connexRelIsLeft y≠x y≤x in rewrite connex_y≤x in
        Refl

public export
0 aminLeft : DecEq a => LinearOrder a rel => rel x y -> ActualMin {rel} x y = x
aminLeft x≤y = case decEq x y of
  Yes Refl => rewrite decEqSelfIsYes {x=y} in Refl
  No x≠y =>
    let (x≠y ** decin) = decEqContraIsNo x≠y in rewrite decin in
    rewrite (connexRelIsLeft x≠y x≤y).snd in Refl

public export
0 maxLeft : DecEq a => LinearOrder a rel => rel x y -> Max' {rel} x y = y
maxLeft x≤y = case decEq x y of
  Yes Refl => rewrite decEqSelfIsYes {x=y} in Refl
  No x≠y =>
    let (x≠y ** decin) = decEqContraIsNo x≠y in rewrite decin in
    rewrite (connexRelIsLeft x≠y x≤y).snd in Refl

public export
0 maxRight : DecEq a => LinearOrder a rel => rel y x -> Not (x = y) -> Max' {rel} x y = x
maxRight y≤x x≠y = case decEq x y of
  Yes Refl => rewrite decEqSelfIsYes {x=y} in Refl
  No x≠y =>
    let (x≠y ** decin) = decEqContraIsNo x≠y in rewrite decin in
    rewrite (connexRelIsRight x≠y y≤x).snd in Refl

public export
(::) : DecEq a => LinearOrder a rel => (x: a) -> Heap {a} {rel} n h -> Heap {a} {rel} (1+n) (min' {n} {rel} x h)
(::) x [] = Singleton x
(::) x (Singleton h) = Prick (ActualMin {rel} x h) (Max' {rel} x h) (min≤max {rel})
(::) x (Prick h s h≤s) =
  Balanced
    (ActualMin {rel} x h)
    (min≤max {rel})
    (minCommutes {rel} \=> minLessThanGreater {rel} h≤s)
    (Singleton (Max' {rel} x h))
    (Singleton s)
(::) x (Balanced {l} {r} h h≤l h≤r left right) =
  Imbalanced
    (ActualMin {rel} x h)
    (smallerLessThanMin {rel} (minCommutes {rel} \=> minLessThanGreater {rel} h≤l) (min≤max {rel}))
    (minCommutes {rel} \=> minLessThanGreater {rel} h≤r)
    ((Max' {rel} x h) :: left)
    right
(::) {n=(1+(2+m)+(1+m))} x (Imbalanced {r} h h≤l h≤r left right) =
  rewrite cong S $ cong S $ cong S $ plusSuccRightSucc (m) (S m) in  (
    Balanced
      (ActualMin {rel} x h)
      (minCommutes {rel} \=> minLessThanGreater {rel} h≤l)
      (smallerLessThanMin {rel} (minCommutes {rel} \=> minLessThanGreater {rel} h≤r) (min≤max {rel}))
      left
      (Max' {rel} x h :: right)
    )

Head: DecEq a => LinearOrder a rel => Heap {a} {rel} (S n) h -> Subset a (\x => x=h)
Head (Singleton h) = Element h Refl
Head (Prick h s h≤s) = Element h Refl
Head (Balanced h h≤l h≤r left right) = Element h Refl
Head (Imbalanced h h≤l h≤r left right) = Element h Refl

public export
0 relationWithHead: DecEq a => LinearOrder a rel => (h: a) -> (Heap {a} {rel} (S n) h') -> Type
relationWithHead {n = 0} h x = ()
relationWithHead {n = (S k)} h x = rel h h'

Tail: DecEq a => LinearOrder a rel => Heap {a} {rel} (S (S n)) h -> (h': a ** Subset (Heap {a} {rel} (S n) h') (\_ => rel h h'))
Tail (Prick h s h≤s) = (s ** Element (Singleton s) h≤s)
Tail (Balanced h h≤l h≤r left right) =
  let Element hl is_l = Head left in
  let Element hr is_r = Head right in
  case order @{SCLeft} {rel} hl hr of
    Left hl≤hr => (hl ** rewrite is_l in Element ?Tail_rhs_2_rhs2_6 h≤l)
    Right hr≤hl => (hr ** rewrite is_r in Element ?Tail_rhs_2_rhs2_7 h≤r)
Tail (Imbalanced h h≤l h≤r left right) = ?Tail_rhs_3

public export
(++) : DecEq a => LinearOrder a rel => Heap {a} {rel} m h -> Heap {a} {rel} n h' -> Heap {a} {rel} (m+n) (min'' {rel} {m} {n} h h')
(++) [] y = y
(++) (Singleton h) y = h::y
(++) (Prick h s h≤s) [] = Prick h s h≤s
(++) (Prick h s h≤s) (Singleton h') =
      Balanced
        (ActualMin {rel} h h')
        (min≤max {rel})
        (minLessThanGreater {rel} h≤s)
        (Singleton (Max' {rel} h h'))
        (Singleton s)
(++) (Prick h s h≤s) (Prick h' s' h'≤s') =
      Imbalanced
        (ActualMin {rel} h h')
        ((congMin {rel} h≤s h'≤s'))
        (min≤max {rel})
        (Prick (ActualMin {rel} s s') (Max' {rel} s s') (min≤max {rel}))
        (Singleton (Max' {rel} h h'))
(++) {n = (1 + ((1 + n) + (1 +n)))} (Prick h s h≤s) (Balanced {l=l'} {r=r'} h' h'≤l' h'≤r' left' right') =
      rewrite solveNat [n] (2 + (1 + ((1 +. n) + (1 +. n)))) (1 + 1 + ((1 +. n) + (2 +. n))) in
        (Balanced
            (ActualMin {rel} h h')
            (smallerLessThanMin {rel} (minCommutes {rel} \=> (minLessThanGreater {rel} h'≤l')) (min≤max {rel}))
            (congMin {rel} h≤s h'≤r')
            (Max' {rel} h h' :: left')
            (s :: right')
          )
(++) {n=1 +((2 +n) + (1+n))} (Prick h s h≤s) (Imbalanced {l=l'} {r=r'} h' h'≤l' h'≤r' left' right') =
      rewrite solveNat [n] (2 + (1 + ((2 +. n) + (1 +. n)))) ((4 +. n) + (2 +. n)) in
        (Imbalanced
          (ActualMin {rel} h h')
          (smallerLessThanMin {rel} (minCommutes {rel} \=> (minLessThanGreater {rel} h'≤l')) (min≤max {rel}))
          (congMin {rel} h≤s h'≤r')
          (Max' {rel} h h' :: left')
          (s :: right')
        )
(++) {m=1+((1+m)+(1+m))} L@(Balanced h h≤l h≤r left right) [] = rewrite solveNat [m] ((1 + ((1 +. m) + (1 +. m))) + 0) ((2 +. m) + (1 +. m)) in L
(++) {m=1+((1+m)+(1+m))} (Balanced {l} {r} h h≤l h≤r left right) (Singleton h') =
      rewrite solveNat [m] ((1 + ((1 +. m) + (1 +. m))) + 1) (3 + ((m .+ (1 +. m)))) in
        (Imbalanced
          (ActualMin {rel} h h')
          (smallerLessThanMin {rel} (minLessThanGreater {rel} h≤l) (min≤max {rel}))
          (minLessThanGreater {rel} h≤r)
          (Max' {rel} h h' :: left)
          right
        )
(++) {m=1+((1+m)+(1+m))} (Balanced {l} {r} h h≤l h≤r left right) (Prick h' s' h'≤s') =
      rewrite solveNat [m] ((1 + ((1 +. m) + (1 +. m))) + 2) (3 + (m .+ (2 +. m))) in
        (Balanced
          (ActualMin {rel} h h')
          (smallerLessThanMin {rel} (minLessThanGreater {rel} h≤l) (min≤max {rel}))
          (congMin {rel} h≤r h'≤s' \=> minCommutes {rel})
          (Max' {rel} h h' :: left)
          (s' :: right)
        )
(++) {m=1+((1+m)+(1+m))} {n=1+((1+n)+(1+n))} (Balanced {l} {r} h h≤l h≤r left right) (Balanced {l=l'} {r=r'} h' h'≤l' h'≤r' left' right') =
      rewrite solveNat [m,n] ((1 + ((1 +. m) + (1 +. m))) + (1 + ((1 +. n) + (1 +. n)))) (3 + ( (m .+ (1 +. n)) + (1 + (m .+ (1 +. n))))) in
        (Imbalanced
          (ActualMin {rel} h h')
          (smallerLessThanMin {rel} (congMin {rel} h≤l h'≤l') (min≤max {rel}))
          (congMin {rel} h≤r h'≤r')
          (Max' {rel} h h' :: (left ++ left'))
          (right ++ right')
        )
(++) {m=1+((1+m)+(1+m))} {n=1+((2+n)+(1+n))} (Balanced {l} {r} h h≤l h≤r left right) (Imbalanced {l=l'} {r=r'} h' h'≤l' h'≤r' left' right') =
      rewrite solveNat [m,n] ((1 + ((1 +. m) + (1 +. m))) + (1 + ((2 +. n) + (1 +. n)))) (3 + ( (m .+ (1 +. n)) + (2 + (m .+ (1 +. n))))) in
        (Balanced
          (ActualMin {rel} h h')
          (congMin {rel} h≤l h'≤l')
          (smallerLessThanMin {rel} (congMin {rel} h≤r h'≤r') (min≤max {rel}))
          (rewrite solveNat [m,n] (1 + ((0 +. m) + (1 +. n))) ((0 +. m) + (2 +. n)) in left++left')
          (Max' {rel} h h' :: (right ++ right'))
        )
(++) {m=1+((2+m)+(1+m))} L@(Imbalanced h h≤l h≤r left right) [] = rewrite solveNat [m] (3 + ((m .+ (1 +. m)) + 0)) (3 +( m .+ (1 +. m))) in L
(++) {m=1+((2+m)+(1+m))} (Imbalanced h h≤l h≤r left right) (Singleton h') =
      rewrite solveNat [m] (3 + ((m .+ (1 +. m)) + 1)) (3 +. m + (2 +. m)) in
        (Balanced
          (ActualMin {rel} h h')
          (minLessThanGreater {rel} h≤l)
          (smallerLessThanMin {rel} (minLessThanGreater {rel} h≤r) (min≤max {rel}))
          left
          (Max' {rel} h h' :: right)
        )
(++) {m=1+((2+m)+(1+m))} (Imbalanced h h≤l h≤r left right) (Prick h' s' h'≤s') =
      rewrite solveNat [m] (3 + ((m .+ (1 +. m)) + 2)) (4 +. m + (2 +. m)) in
        (Imbalanced
          (ActualMin {rel} h h')
          (smallerLessThanMin {rel} (minLessThanGreater {rel} h≤l) (min≤max {rel}))
          (minCommutes {rel} \=> congMin {rel} h'≤s' h≤r)
          (Max' {rel} h h' :: left)
          (s' :: right)
        )
(++) {m=1+((2+m)+(1+m))} {n=1+((1+n)+(1+n))} (Imbalanced h h≤l h≤r left right) (Balanced h' h'≤l' h'≤r' left' right') =
      rewrite solveNat [m,n] (3+.m + (1+.m) + (2+.n + (1+.n))) (3 + ( (m .+ (1 +. n)) + (2 + (m .+ (1 +. n))))) in
        (Balanced
          (ActualMin {rel} h h')
          (congMin {rel} h≤l h'≤l')
          (smallerLessThanMin {rel} (congMin {rel} h≤r h'≤r') (min≤max {rel}))
          (left ++ left')
          (Max' {rel} h h' :: (right ++ right'))
        )
(++) {m=1+((2+m)+(1+m))} {n=1+((2+n)+(1+n))} (Imbalanced h h≤l h≤r left right) (Imbalanced h' h'≤l' h'≤r' left' right') =
      rewrite solveNat [m,n] (3+.m + (1+.m) + (3+.n + (1+.n))) (4 + ( (m .+ (1 +. n)) + (2 + (m .+ (1 +. n))))) in
        (Imbalanced
            (ActualMin {rel} h h')
            (congMin {rel} h≤l h'≤l')
            (smallerLessThanMin {rel} (congMin {rel} h≤r h'≤r') (min≤max {rel}))
            (rewrite solveNat [m,n] (1 + ((0 +. m) + (1 +. n))) ((0 +. m) + (2 +. n)) in left ++ left')
            (Max' {rel} h h' :: right ++ right')
          )

public export
cnt : DecEq a => LinearOrder a rel => (x: a) -> (xs: Heap {rel} n h) -> Nat
cnt x [] = 0
cnt x (Singleton h) = case decEq x h of
  Yes Refl => 1
  No _ => 0
cnt x (Prick h s hs) = case decEq x h of
  Yes Refl => case decEq x s of
    Yes Refl => 2
    No _ => 1
  No _ => case decEq x s of
    Yes Refl => 1
    No _ => 0
cnt x (Balanced h {l} {r} hl hr left right) = case decEq x h of
  Yes Refl => 1 + cnt x left + cnt x right
  No x≠h => case connex {rel} x≠h of
    Left x≤h => 0
    Right h≤x => cnt x left + cnt x right
cnt x (Imbalanced h hl hr left right)  = case decEq x h of
  Yes Refl => 1 + cnt x left + cnt x right
  No x≠h => case connex {rel} x≠h of
    Left _ => 0
    Right _ => cnt x left + cnt x right

interface Choice (0 f: a->b->c) where
  0 choice: forall x, y. Either (f x y = x) (f x y = y)

public export
[CHAMIN] DecEq a => LinearOrder a rel => Choice (ActualMin {rel}) where
  choice {x} {y} = case decEq x y of
    Yes Refl => rewrite decEqSelfIsYes {x=y} in Left Refl
    No x≠y =>
      let (x≠y ** decin) = decEqContraIsNo x≠y in rewrite decin in case connex {rel} x≠y of
      Left x≤y => rewrite (connexRelIsLeft x≠y x≤y).snd in Left Refl
      Right y≤x => rewrite (connexRelIsRight x≠y y≤x).snd in Right Refl

public export
[CHMAX] DecEq a => LinearOrder a rel => Choice (Max' {rel}) where
  choice {x} {y} = case decEq x y of
    Yes Refl => rewrite decEqSelfIsYes {x=y} in Left Refl
    No x≠y =>
      let (x≠y ** decin) = decEqContraIsNo x≠y in rewrite decin in case connex {rel} x≠y of
      Left x≤y => rewrite (connexRelIsLeft x≠y x≤y).snd in Right Refl
      Right y≤x => rewrite (connexRelIsRight x≠y y≤x).snd in Left Refl

neither: Choice f => Not (x=y) -> Not (x=z) -> Not (x=f y z)
neither x≠y x≠z prf = void $ case choice {f} {x=y} {y=z} of
  (Left w) => x≠y (prf \=> w)
  (Right w) => x≠z (prf \=> w)

export
0 strict : DecEq a => LinearOrder a rel  => (x≠h: (x=h -> Void)) -> (x≤h: rel x h) -> (h≤s: rel h s) -> x=s -> Void
strict x≠h x≤h h≤s Refl = void $ x≠h (antisymmetric x≤h h≤s)

export
0 cntTooSmall : DecEq a => LinearOrder a rel => (x: a) -> (x≠h: (x=h -> Void)) -> (x≤h: rel x h) -> (xs: Heap {rel} (S n) h) -> cnt x xs = 0
cntTooSmall x x≠h x≤h (Singleton h) = rewrite snd $ decEqContraIsNo x≠h in Refl
cntTooSmall x x≠h x≤h (Prick h s h≤s) =
  rewrite snd $ decEqContraIsNo x≠h in
  rewrite snd $ decEqContraIsNo (strict {rel} x≠h x≤h h≤s) in
  Refl
cntTooSmall x x≠h x≤h (Balanced h h≤l h≤r left right) =
  let (x≠h ** decno) = decEqContraIsNo x≠h in rewrite decno in
  let (x≤h ** connex_x≤h) = connexRelIsLeft x≠h x≤h in rewrite connex_x≤h in
  Refl
cntTooSmall x x≠h x≤h (Imbalanced h h≤l h≤r left right) =
  let (x≠h ** decno) = decEqContraIsNo x≠h in rewrite decno in
  let (x≤h ** connex_x≤h) = connexRelIsLeft x≠h x≤h in rewrite connex_x≤h in
  Refl

public export
[ui] DecEq a => LinearOrder a rel => (xs: Heap {rel} (S n) h) => Uninhabited (forall x . cnt {rel} {n=S n} x xs = 0) where
    uninhabited {xs = (Singleton h)} absrd = SIsNotZ $ ((rewrite decEqSelfIsYes {x=h} in Refl) \=> absrd {x=h})
    uninhabited {xs = (Prick h s h≤s)} absrd with (decEq h s)
      uninhabited {xs = (Prick h h h≤s)} absrd | (Yes Refl) = SIsNotZ $ ((rewrite decEqSelfIsYes {x=h} in rewrite decEqSelfIsYes {x=h} in Refl) \=> absrd {x=h})
      uninhabited {xs = (Prick h s h≤s)} absrd | (No h≠s) = SIsNotZ $ ((rewrite decEqSelfIsYes {x=h} in rewrite (decEqContraIsNo h≠s).snd in Refl) \=> absrd {x=h})
    uninhabited {xs = (Balanced h h≤l h≤r left right)} absrd = SIsNotZ $ ((rewrite decEqSelfIsYes {x=h} in Refl) \=> absrd {x=h})
    uninhabited {xs = (Imbalanced h h≤l h≤r left right)} absrd = SIsNotZ $ ((rewrite decEqSelfIsYes {x=h} in Refl) \=> absrd {x=h})

0 ConsAddsOne': DecEq a => LinearOrder a rel => (0 xs: Heap {rel} n h) -> forall x. (1 + cnt x xs) = cnt x ((x :: xs) {rel})
ConsAddsOne' {h} xs with (wellFounded {rel=LT} n)
  ConsAddsOne' {h=()} [] | acc = rewrite decEqSelfIsYes {x} in Refl
  ConsAddsOne' {h} (Singleton h) | acc with (decEq x h)
    ConsAddsOne' {h} (Singleton h) | acc | (Yes Refl) =
      rewrite decEqSelfIsYes {x=h} in
      rewrite decEqSelfIsYes {x=h} in Refl
    ConsAddsOne' {h} (Singleton h) | acc | (No x≠h) with (connex {rel} x≠h)
      ConsAddsOne' {h} (Singleton h) | acc | (No x≠h) | (Left x≤h) =
        rewrite decEqSelfIsYes {x} in
        rewrite (decEqContraIsNo x≠h).snd in Refl
      ConsAddsOne' {h} (Singleton h) | acc | (No x≠h) | (Right h≤x) =
        rewrite (decEqContraIsNo x≠h).snd in
        rewrite decEqSelfIsYes {x} in Refl
  ConsAddsOne' {h} (Prick h s h≤s) | acc with (decEq x h)
    ConsAddsOne' {h} (Prick h s h≤s) | acc | (Yes Refl) with (decEq h s)
      ConsAddsOne' {h} (Prick s s h≤s) | acc | (Yes Refl) | (Yes Refl) =
        rewrite decEqSelfIsYes {x=s} in rewrite decEqSelfIsYes {x=s} in Refl
      ConsAddsOne' {h} (Prick h s h≤s) | acc | (Yes Refl) | (No h≠s) =
        rewrite decEqSelfIsYes {x=h} in
        rewrite decEqSelfIsYes {x=h} in
        rewrite (decEqContraIsNo h≠s).snd in Refl
    ConsAddsOne' {h} (Prick h s h≤s) | acc | (No x≠h) with (decEq x s)
      ConsAddsOne' {h} (Prick h s h≤s) | acc | (No s≠h) | (Yes Refl) =
        let (h≤s ** connex_h≤s) = connexRelIsRight s≠h h≤s in rewrite connex_h≤s in
        let (s≠h ** decno) = decEqContraIsNo $ negEqSym s≠h in rewrite decno in 
        let (h≤s ** connex_h≤s) = connexRelIsLeft s≠h h≤s in rewrite connex_h≤s in
        let (s≠h ** decno) = decEqContraIsNo $ negEqSym s≠h in rewrite decno in 
        let (h≤s ** connex_h≤s) = connexRelIsRight s≠h h≤s in rewrite connex_h≤s in
        rewrite decEqSelfIsYes {x=s} in Refl
      ConsAddsOne' {h} (Prick h s h≤s) | acc | (No x≠h) | (No x≠s) with (connex {rel} x≠h)
        ConsAddsOne' {h} (Prick h s h≤s) | acc | (No x≠h) | (No x≠s) | (Left x≤h) =
          rewrite decEqSelfIsYes {x} in rewrite (decEqContraIsNo x≠h).snd in rewrite (decEqContraIsNo x≠s).snd in Refl
        ConsAddsOne' {h} (Prick h s h≤s) | acc | (No x≠h) | (No x≠s) | (Right h≤x) =
          let (h≠x ** decno) = decEqContraIsNo $ negEqSym x≠h in rewrite decno in
          let (x≠h ** decno) = decEqContraIsNo x≠h in rewrite decno in
          let (h≤x ** connex_h≤x) = connexRelIsLeft h≠x h≤x in rewrite connex_h≤x in
          let (h≤x ** connex_h≤x) = connexRelIsRight x≠h h≤x in rewrite connex_h≤x in
          rewrite decEqSelfIsYes {x} in rewrite (decEqContraIsNo x≠s).snd in Refl
  ConsAddsOne' {h} (Balanced h h≤l h≤r left right) | acc with (decEq x h)
    ConsAddsOne' {h} (Balanced h h≤l h≤r left right) | (Access acc) | (Yes Refl) =
      rewrite decEqSelfIsYes {x=h} in
      cong (\l => S(l + cnt h right))
        (ConsAddsOne' left | acc _ $ LTESucc $ LTESucc $ lteAddRight _)
    ConsAddsOne' {h} (Balanced h h≤l h≤r left right) | acc | (No x≠h) with (connex {rel} x≠h)
      ConsAddsOne' {h} (Balanced h h≤l h≤r left right) | acc | (No x≠h) | (Left x≤h) =
        rewrite decEqSelfIsYes {x} in
          cong S (sym (cong2 (+)
            (cntTooSmall {rel} x (\x_minhl => x≠h (x_minhl \=> (aminLeft h≤l))) (smallerLessThanMin {rel} (x≤h \=> h≤l) x≤h) _)
            (cntTooSmall {rel} x (strict x≠h x≤h h≤r) (x≤h \=> h≤r) _)
          ))
      ConsAddsOne' {h} (Balanced h h≤l h≤r left right) | (Access acc) | (No x≠h) | (Right h≤x) =
        let (h≠x ** decno) = decEqContraIsNo $ negEqSym x≠h in rewrite decno in
        let (h≤x ** connex_h≤x) = connexRelIsLeft h≠x h≤x in rewrite connex_h≤x in
        let (x≠h ** decno) = decEqContraIsNo x≠h in rewrite decno in
        let (h≤x ** connex_h≤x) = connexRelIsRight x≠h h≤x in rewrite connex_h≤x in
        cong (+ (cnt x right)) (ConsAddsOne' left | acc _ $ LTESucc $ LTESucc $ lteAddRight _)
  ConsAddsOne' {h} (Imbalanced h h≤l h≤r left right) | acc with (decEq x h)
    ConsAddsOne' {h} (Imbalanced h h≤l h≤r left right) | (Access acc) | (Yes Refl) =
      rewrite decEqSelfIsYes {x=h} in
      cong S ((plusSuccRightSucc _ _) \=> cong (cnt h left +) (ConsAddsOne' right | acc _ (LTESucc (LTESucc (lteSuccRight $ lteAddRight _)))))
    ConsAddsOne' {h} (Imbalanced h h≤l h≤r left right) | acc | (No x≠h) with (connex {rel} x≠h)
      ConsAddsOne' {h} (Imbalanced h h≤l h≤r left right) | acc | (No x≠h) | (Left x≤h) =
        rewrite decEqSelfIsYes {x} in
          cong S (
            cong2 (+)
              (sym $ cntTooSmall {rel} x (strict x≠h x≤h h≤l) (x≤h \=> h≤l) left)
              (sym $ cntTooSmall {rel} x (strict {rel} x≠h x≤h (smallerLessThanMin {rel} h≤r reflexive)) (smallerLessThanMin {rel} (x≤h \=> h≤r) x≤h) (h::right))
            )
      ConsAddsOne' {h} (Imbalanced h h≤l h≤r left right) | (Access acc) | (No x≠h) | (Right h≤x) =
        let (h≠x ** decno) = decEqContraIsNo $ negEqSym x≠h in rewrite decno in
        let (h≤x ** connex_h≤x) = connexRelIsLeft h≠x h≤x in rewrite connex_h≤x in
        let (x≠h ** decno) = decEqContraIsNo x≠h in rewrite decno in
        let (h≤x ** connex_h≤x) = connexRelIsRight x≠h h≤x in rewrite connex_h≤x in
        plusSuccRightSucc _ _ \=> cong (cnt x left +) (ConsAddsOne' right | acc _ (LTESucc (LTESucc (lteSuccRight $ lteAddRight _))))

public export
ConsAddsOne: DecEq a => LinearOrder a rel => (0 x: a) -> (0 xs: Heap {rel} n h) -> (1 + cnt x xs) = cnt x (x::  xs)
ConsAddsOne x xs = rewrite ConsAddsOne' xs {x} in Refl

public export
eitherIndifferent: {x, y, z: a} -> {c: Either a' a''} -> (same_y: x = y) -> (same_z: x = z) -> Lazy (x = case c of {Left _ => y; Right _ => z})
eitherIndifferent {c = (Left _)} eq _ = eq
eitherIndifferent {c = (Right _)} _ eq = eq

0 ConsKeepsRest': DecEq a => LinearOrder a rel => {x, x': a} -> {xs: Heap {rel} n h} -> (x'≠x: Not (x' = x)) -> cnt x' xs = cnt x' (x :: xs)
ConsKeepsRest' {n} {h} {x} {x'} {xs} x'≠x with (wellFounded {rel=LT} n)
  ConsKeepsRest' {n=0} {h = ()} {x} {x'} {xs = []} x'≠x | acc = rewrite (decEqContraIsNo x'≠x).snd in Refl
  ConsKeepsRest' {n=1} {h} {x} {x'} {xs = (Singleton h)} x'≠x | acc with (decEq x' h)
    ConsKeepsRest' {n=1} {h} {x} {x'=_} {xs = (Singleton h)} h≠x | acc | (Yes Refl) =
      let (x≠h ** decno) = decEqContraIsNo $ negEqSym h≠x in rewrite decno in case connex {rel} x≠h of
        (Left x≤h) =>
          let (x≤h ** connex_x≤h) = connexRelIsLeft x≠h x≤h in rewrite connex_x≤h in
          let (h≠x ** decno) = decEqContraIsNo h≠x in rewrite decno in
          rewrite decEqSelfIsYes {x=h} in Refl
        (Right h≤x) =>
          let (h≤x ** connex_h≤x) = connexRelIsRight x≠h h≤x in rewrite connex_h≤x in
          rewrite decEqSelfIsYes {x=h} in
          let (h≠x ** decno) = decEqContraIsNo h≠x in rewrite decno in Refl
    ConsKeepsRest' {n=1} {h} {x} {x'} {xs = (Singleton h)} x'≠x | acc | (No x'≠h) =
      let (x'≠min_x_h ** decno) = decEqContraIsNo (neither @{CHAMIN {a} {rel}} x'≠x x'≠h) in rewrite decno in
      let (x'≠max_x_h ** decno) = decEqContraIsNo (neither @{CHMAX {a} {rel}} x'≠x x'≠h) in rewrite decno in
      Refl
  ConsKeepsRest' {n=2} {h} {x} {x'} {xs = (Prick h s h≤s)} x'≠x | acc with (decEq x' h)
    ConsKeepsRest' {n=2} {h} {x} {x'=_} {xs = (Prick h s h≤s)} h≠x | acc | (Yes Refl) =
      let (x≠h ** decno) = decEqContraIsNo $ negEqSym h≠x in rewrite decno in case connex {rel} x≠h of
        (Left x≤h) =>
          let (x≤h ** connex_x≤h) = connexRelIsLeft x≠h x≤h in rewrite connex_x≤h in
          let (h≠x ** decno) = decEqContraIsNo h≠x in rewrite decno in
          let (x≤h ** connex_x≤h) = connexRelIsRight h≠x x≤h in rewrite connex_x≤h in
          rewrite decEqSelfIsYes {x=h} in
          case decEq h s of
            (Yes Refl) =>
              rewrite decEqSelfIsYes {x=h} in Refl
            (No h≠s) =>
              let (h≠s ** decno) = decEqContraIsNo h≠s in rewrite decno in Refl
        (Right h≤x) =>
          let (h≤x ** connex_h≤x) = connexRelIsRight x≠h h≤x in rewrite connex_h≤x in
          let (h≠x ** decno) = decEqContraIsNo h≠x in rewrite decno in
          let (h≤x ** connex_h≤x) = connexRelIsLeft h≠x h≤x in rewrite connex_h≤x in
          rewrite decEqSelfIsYes {x=h} in
          let (h≠x ** decno) = decEqContraIsNo h≠x in rewrite decno in
          case decEq h s of
            (Yes Refl) =>
              rewrite decEqSelfIsYes {x=h} in Refl
            (No h≠s) =>
              let (h≠s ** decno) = decEqContraIsNo h≠s in rewrite decno in Refl
    ConsKeepsRest' {n=2} {h} {x} {x'} {xs = (Prick h s h≤s)} x'≠x | acc | (No x'≠h) =
      let (x'≠min_x_h ** decno) = decEqContraIsNo (neither @{CHAMIN {a} {rel}} x'≠x x'≠h) in rewrite decno in
      case decEq x' s of
        (Yes Refl) =>
          rewrite decEqSelfIsYes {x=x'} in
          let (min_x_h≤x' ** connex_min_x_h≤x') = connexRelIsRight {rel} x'≠min_x_h $ (minCommutes {rel} \=> minLessThanGreater {h} {h'=x} {rel} h≤s) in
          rewrite connex_min_x_h≤x' in
          rewrite decEqSelfIsYes {x=x'} in
          let (x'≠max_x_h ** decno) = decEqContraIsNo (neither @{CHMAX {a} {rel}} x'≠x x'≠h) in rewrite decno in
          Refl
        (No x'≠s) =>
          let (x'≠s ** decin) = decEqContraIsNo x'≠s in rewrite decin in
          case connexIsEither {rel} x'≠min_x_h of
            Left (x≤h ** connex_x≤h) => rewrite connex_x≤h in Refl
            Right (h≤x ** connex_h≤x) => rewrite connex_h≤x in
              let (x'≠s ** decno) = decEqContraIsNo x'≠s in rewrite decno in
              let (x'≠max_x_h ** decno) = decEqContraIsNo (neither @{CHMAX {a} {rel}} x'≠x x'≠h) in rewrite decno in
              Refl
  ConsKeepsRest' {n = 1 + ((1 + m) + (1 + m))} {h} {x} {x'} {xs = (Balanced h h≤l h≤r left right)} x'≠x | acc with (decEq x' h)
    ConsKeepsRest' {n = 1 + ((1 + m) + (1 + m))} {h} {x} {x'=h} {xs = (Balanced h h≤l h≤r left right)} h≠x | Access acc | (Yes Refl) =
      let (x≠h ** decno) = decEqContraIsNo $ negEqSym h≠x in rewrite decno in case connex {rel} x≠h of
        (Left x≤h) =>
          let (x≤h ** connex_x≤h) = connexRelIsLeft x≠h x≤h in rewrite connex_x≤h in
          let (h≠x ** decno) = decEqContraIsNo h≠x in rewrite decno in
          let (x≤h ** connex_x≤h) = connexRelIsRight h≠x x≤h in rewrite connex_x≤h in
          cong (+ (cnt h right)) (ConsAddsOne h left)
        (Right h≤x) =>
          let (h≤x ** connex_h≤x) = connexRelIsRight x≠h h≤x in rewrite connex_h≤x in
          let (h≠x ** decno) = decEqContraIsNo h≠x in rewrite decno in
          let (h≤x ** connex_h≤x) = connexRelIsLeft h≠x h≤x in rewrite connex_h≤x in
          rewrite decEqSelfIsYes {x=h} in
          cong S $ cong (+ (cnt h right)) $
          ConsKeepsRest' h≠x | acc (S m) (LTESucc $ LTESucc $ lteAddRight _)
    ConsKeepsRest' {n = 1 + ((1 + m) + (1 + m))} {h} {x} {x'} {xs = (Balanced h h≤l h≤r left right)} x'≠x | acc | (No x'≠h) with (connex {rel} x'≠h)
      ConsKeepsRest' {n = 1 + ((1 + m) + (1 + m))} {h} {x} {x'} {xs = (Balanced h h≤l h≤r left right)} x'≠x | Access acc | (No x'≠h) | (Left x'≤h) =
        let (x'≠min_x_h ** decno) = decEqContraIsNo (neither @{CHAMIN {a} {rel}} x'≠x x'≠h) in
        rewrite decno in case connexIsEither {rel} x'≠min_x_h of
          Left (x'≤min_x_h ** connex_x'≤min_x_h) => rewrite connex_x'≤min_x_h in Refl
          Right (min_x_h≤x' ** connex_min_x_h≤x') => rewrite connex_min_x_h≤x' in
            let
              cts = sym $ cntTooSmall x' (strict {rel} x'≠h x'≤h h≤r) (x'≤h \=> h≤r) right
              ctt = sym $ cntTooSmall x' (strict {rel} x'≠h x'≤h h≤l) (x'≤h \=> h≤l) left
              ckr = (ConsKeepsRest' {xs = left} (neither @{CHMAX {a} {rel}} x'≠x x'≠h) | acc _ (LTESucc $ LTESucc $ lteAddRight _))
              cttkr = ctt \=> ckr
            in cong2 (+) cttkr cts
      ConsKeepsRest' {n = 1 + ((1 + m) + (1 + m))} {h} {x} {x'} {xs = (Balanced h h≤l h≤r left right)} x'≠x | Access acc | (No x'≠h) | (Right h≤x') =
        let (x'≠min_x_h ** decno) = decEqContraIsNo (neither @{CHAMIN {a} {rel}} x'≠x x'≠h) in rewrite decno in
        let (min_x_h≤x' ** connex_min_x_h≤x') = connexRelIsRight {rel} x'≠min_x_h (minLessThanGreater' {a} {rel} h≤x') in rewrite connex_min_x_h≤x' in
          cong (+ (cnt x' right)) $
          (ConsKeepsRest' (neither @{CHMAX {a} {rel}} x'≠x x'≠h) | acc (S m) (LTESucc $ LTESucc $ lteAddRight _))
  ConsKeepsRest' {n = 1 + ((2 + m) + (1 + m))} {h} {x} {x'} {xs = (Imbalanced h h≤l h≤r left right)} x'≠x | acc with (decEq x' h)
    ConsKeepsRest' {n = 1 + ((2 + m) + (1 + m))} {h} {x} {x'=h} {xs = (Imbalanced h h≤l h≤r left right)} x'≠x | Access acc | (Yes Refl) =
      let (x≠h ** decno) = decEqContraIsNo $ negEqSym x'≠x in rewrite decno in case connex {rel} x≠h of
        (Left x≤h) =>
          let (x≤h ** connex_x≤h) = connexRelIsLeft x≠h x≤h in rewrite connex_x≤h in
          let (h≠x ** decno) = decEqContraIsNo x'≠x in rewrite decno in
          let (x≤h ** connex_x≤h) = connexRelIsRight h≠x x≤h in rewrite connex_x≤h in
          plusSuccRightSucc _ _ \=> cong (cnt h left +) (ConsAddsOne h right)
        (Right h≤x) =>
          let (h≤x ** connex_h≤x) = connexRelIsRight x≠h h≤x in rewrite connex_h≤x in
          let (h≠x ** decno) = decEqContraIsNo x'≠x in rewrite decno in
          let (h≤x ** connex_h≤x) = connexRelIsLeft h≠x h≤x in rewrite connex_h≤x in
          rewrite decEqSelfIsYes {x=h} in
          cong (S (cnt h left) + ) $
          ConsKeepsRest' h≠x | acc (S m) (LTESucc $ LTESucc $ lteSuccRight $ lteAddRight _)
    ConsKeepsRest' {n = 1 + ((2 + m) + (1 + m))} {h} {x} {x'} {xs = (Imbalanced h h≤l h≤r left right)} x'≠x | Access acc | (No x'≠h) =
      let (x'≠min_x_h ** decno) = decEqContraIsNo (neither @{CHAMIN {a} {rel}} x'≠x x'≠h) in rewrite decno in
      case connexIsEither {rel} x'≠h of
        Left (x'≤h ** connex_x'≤h) => rewrite connex_x'≤h in case connexIsEither {rel} x'≠min_x_h of
          Left (x'≤min_x_h ** connex_x'≤min_x_h) => rewrite connex_x'≤min_x_h in Refl
          Right (min_x_h≤x' ** connex_min_x_h≤x') => rewrite connex_min_x_h≤x' in
            let
              cts = sym $ cntTooSmall x' (strict {rel} x'≠h x'≤h h≤r) (x'≤h \=> h≤r) right
              ctt = sym $ cntTooSmall x' (strict {rel} x'≠h x'≤h h≤l) (x'≤h \=> h≤l) left
              ckr = (ConsKeepsRest' {xs = right} (neither @{CHMAX {a} {rel}} x'≠x x'≠h) | acc _ (LTESucc $ LTESucc $ lteSuccRight $ lteAddRight _))
              ctskr = cts \=> ckr
            in cong2 (+) ctt ctskr
        Right (h≤x' ** connex_h≤x') => rewrite connex_h≤x' in
          let (min_x_h≤x' ** connex_min_x_h≤x') = connexRelIsRight {rel} x'≠min_x_h (minLessThanGreater' {a} {rel} h≤x') in rewrite connex_min_x_h≤x' in
          cong ((cnt x' left) +) $
          (ConsKeepsRest' (neither @{CHMAX {a} {rel}} x'≠x x'≠h) | acc (S m) (LTESucc $ LTESucc $ lteSuccRight $ lteAddRight _))

public export
ConsKeepsRest: DecEq a => LinearOrder a rel => {0 x, x': a} -> {0 xs: Heap n h} -> (0 x'≠x: Not (x' = x)) -> (cnt {rel} {n} x' xs) = cnt {rel} {n=S n} x' (Heap.(::) {rel} x xs)
ConsKeepsRest x'≠x = rewrite ConsKeepsRest' {x} {x'} {xs} x'≠x in Refl
