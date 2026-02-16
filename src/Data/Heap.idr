module Data.Heap

import Algebra.Solver.Semiring
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

export
Maybe' : Nat -> Type -> Type
Maybe' 0 _ = ()
Maybe' (S _) ty = ty

public export
data Heap : LinearOrder a rel => (n: Nat) -> (h: Maybe' n a) -> Type where
    Nil : Heap @{lo} 0 ()
    Singleton: (h: a) -> Heap @{lo} {a} 1 h
    Prick : (h: a) -> (s: a) -> (0 h≤s: rel h s) -> Heap @{lo} {rel} 2 h
    Balanced : (h: a) -> (0 h≤l: rel h l) -> (0 h≤r: rel h r) -> (left: Heap @{lo} (1+m) l) -> (right: Heap @{lo} (1+m) r) -> Heap @{lo} {rel} (3+m+m) h
    Imbalanced : (h: a) -> (0 h≤l: rel h l) -> (0 h≤r: rel h r) -> (left: Heap @{lo} (2 + m) l) -> (right: Heap @{lo} (1+m) r) -> Heap @{lo} {rel} (4+m+m) h

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
actualMin :  DecEq a => LinearOrder a rel => a -> a -> a
actualMin x y with (decEq x y)
  actualMin x x | (Yes Refl) = x
  actualMin x y | (No x≠y) with (connex {rel} x≠y)
    actualMin x y | (No x≠y) | Left x≤y = x
    actualMin x y | (No x≠y) | Right y≤x = y


public export
min' : DecEq a => LinearOrder a rel => {n: Nat} -> a -> Maybe' n a -> a
min' {n = 0} x _ = x
min' {n = (S k)} x y = actualMin {rel} x y


public export
max' : DecEq a => LinearOrder a rel => a -> a -> a
max' x y with (decEq x y)
  max' x x | (Yes Refl) = x
  max' x y | (No x≠y) with (connex {rel} x≠y)
    max' x y | (No x≠y) | (Left x≤y) = y
    max' x y | (No x≠y) | (Right y≤x) = x

public export
min'' : DecEq a => LinearOrder a rel => {m, n: Nat} -> Maybe' m a -> Maybe' n a -> Maybe' (m+n) a
min'' {m = 0} _ x = rewrite plusZeroLeftNeutral n in x
min'' {m = (S k)} x y = min' {rel} x y

public export
smallerLessThanMin : DecEq a => LinearOrder a rel => {h, h', l: a} -> (h≤l: rel h l) -> (h≤h': rel h h') -> rel h (actualMin {rel} h' l)
smallerLessThanMin h≤l h≤h' with (decEq h' l)
  smallerLessThanMin h≤l h≤h' | (Yes Refl) = h≤l
  smallerLessThanMin h≤l h≤h' | (No h'≠l) with (connex {rel} h'≠l)
    smallerLessThanMin h≤l h≤h' | (No h'≠l) | (Left h'≤l) = h≤h'
    smallerLessThanMin h≤l h≤h' | (No h'≠l) | (Right l≤h') = h≤l

public export
minLessThanGreater : DecEq a => LinearOrder a rel => {h, h', l: a} -> (h≤l: rel h l) -> rel (actualMin {rel} h h') l
minLessThanGreater h≤l with (decEq h h')
  minLessThanGreater h≤l | (Yes Refl) = h≤l
  minLessThanGreater h≤l | (No h≠h') with (connex {rel} h≠h')
    minLessThanGreater h≤l | (No h≠h') | (Left h≤h') = h≤l
    minLessThanGreater h≤l | (No h≠h') | (Right h'≤h) = (h'≤h \=> h≤l)

public export
congMin : DecEq a => LinearOrder a rel => {h, h', l, l': a} -> (h≤l: rel h l) -> (h'≤l': rel h' l') -> rel (actualMin {rel} h h') (actualMin {rel} l l')
congMin h≤l h'≤l' with (decEq h h')
  congMin h≤l h≤l' | (Yes Refl) = smallerLessThanMin {rel} h≤l' h≤l
  congMin h≤l h'≤l' | (No h≠h') with (connex {rel} h≠h')
    congMin h≤l h'≤l' | (No h≠h') | (Left h≤h') = smallerLessThanMin {rel} (h≤h' \=> h'≤l') h≤l
    congMin h≤l h'≤l' | (No h≠h') | (Right h'≤h) = smallerLessThanMin {rel} h'≤l' (h'≤h \=> h≤l)

public export
min≤max : DecEq a => LinearOrder a rel => {h, h': a} -> rel (actualMin {rel} h h') (max' {rel} h h')
min≤max with (decEq h h')
  min≤max | (Yes Refl) = reflexive
  min≤max | (No h≠h') with (connex {rel} h≠h')
    min≤max | (No h≠h') | (Left h≤h') = h≤h'
    min≤max | (No h≠h') | (Right h'≤h) = h'≤h

public export
minCommutes : DecEq a => LinearOrder a rel => {h, h': a} -> rel (actualMin {rel} h h') (actualMin {rel} h' h)
minCommutes with (decEq h h')
  minCommutes | (Yes Refl) = rewrite decEqSelfIsYes {x=h'} in reflexive
  minCommutes | (No h≠h') with (connex {rel} h≠h')
    minCommutes | (No h≠h') | (Left h≤h') = (smallerLessThanMin {rel} reflexive h≤h')
    minCommutes | (No h≠h') | (Right h'≤h) = (smallerLessThanMin {rel} h'≤h reflexive)

public export
minCom : DecEq a => LinearOrder a rel => {x, y: a} -> actualMin {rel} x y = actualMin {rel} y x
minCom with (decEq x y)
  minCom | (Yes Refl) = rewrite decEqSelfIsYes {x=y} in Refl
  minCom | (No x≠y) =
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
0 aminLeft : DecEq a => LinearOrder a rel => rel x y -> actualMin {rel} x y = x
aminLeft x≤y with (decEq x y)
  aminLeft x≤y | (Yes Refl) = Refl
  aminLeft x≤y | (No x≠y) = rewrite (connexRelIsLeft x≠y x≤y).snd in Refl

public export
0 maxLeft : DecEq a => LinearOrder a rel => rel x y -> max' {rel} x y = y
maxLeft x≤y with (decEq x y)
  maxLeft x≤y | (Yes Refl) = Refl
  maxLeft x≤y | (No x≠y) with (connex {rel} x≠y)
    maxLeft _ | (No x≠y) | (Left x≤y) = Refl
    maxLeft x≤y | (No x≠y) | (Right y≤x) = void $ x≠y (antisymmetric x≤y y≤x)

public export
0 maxRight : DecEq a => LinearOrder a rel => rel y x -> Not (x = y) -> max' {rel} x y = x
maxRight y≤x x≠y with (decEq x y)
  maxRight y≤x x≠y | (Yes Refl) = Refl
  maxRight y≤x _ | (No x≠y) with (connex {rel} x≠y)
    maxRight y≤x _ | (No x≠y) | (Left x≤y) = void $ x≠y (antisymmetric x≤y y≤x)
    maxRight _ _ | (No x≠y) | (Right y≤x) = Refl


public export
(::) : DecEq a => LinearOrder a rel => (x: a) -> Heap {a} {rel} n h -> Heap {a} {rel} (1+n) (min' {n} {rel} x h)
(::) x [] = Singleton x
(::) x (Singleton h) = Prick (actualMin {rel} x h) (max' {rel} x h) (min≤max {rel})
(::) x (Prick h s h≤s) =
  Balanced
    (actualMin {rel} x h)
    (min≤max {rel})
    (minCommutes {rel} \=> minLessThanGreater {rel} h≤s)
    (Singleton (max' {rel} x h))
    (Singleton s)
(::) x (Balanced {l} {r} h h≤l h≤r left right) =
  Imbalanced
    (actualMin {rel} x h)
    (smallerLessThanMin {rel} (minCommutes {rel} \=> minLessThanGreater {rel} h≤l) (min≤max {rel}))
    (minCommutes {rel} \=> minLessThanGreater {rel} h≤r)
    ((max' {rel} x h) :: left)
    right
(::) {n=4+m+m} x (Imbalanced {r} h h≤l h≤r left right) =
  rewrite plusSuccRightSucc m m in (
    Balanced
      (actualMin {rel} x h)
      (minCommutes {rel} \=> minLessThanGreater {rel} h≤l)
      (smallerLessThanMin {rel} (minCommutes {rel} \=> minLessThanGreater {rel} h≤r) (min≤max {rel}))
      left
      (max' {rel} x h :: right)
    )

public export
(++) : DecEq a => LinearOrder a rel => Heap {a} {rel} m h -> Heap {a} {rel} n h' -> Heap {a} {rel} (m+n) (min'' {rel} {m} {n} h h')
(++) [] y = y
(++) (Singleton h) y = h::y
(++) (Prick h s h≤s) [] = Prick h s h≤s
(++) (Prick h s h≤s) (Singleton h') =
      Balanced
        (actualMin {rel} h h')
        (min≤max {rel})
        (minLessThanGreater {rel} h≤s)
        (Singleton (max' {rel} h h'))
        (Singleton s)
(++) (Prick h s h≤s) (Prick h' s' h'≤s') =
      Imbalanced
        (actualMin {rel} h h')
        ((congMin {rel} h≤s h'≤s'))
        (min≤max {rel})
        (Prick (actualMin {rel} s s') (max' {rel} s s') (min≤max {rel}))
        (Singleton (max' {rel} h h'))
(++) {n = ((3 + n) + n)} (Prick h s h≤s) (Balanced {l=l'} {r=r'} h' h'≤l' h'≤r' left' right') =
      rewrite solveNat [n] (1 + ((0 +. n) +. n)) ((0 +. n) + (0 + (1 +. n))) in
        (Balanced
          (actualMin {rel} h h')
          (smallerLessThanMin {rel} (minCommutes {rel} \=> (minLessThanGreater {rel} h'≤l')) (min≤max {rel}))
          (congMin {rel} h≤s h'≤r')
          (max' {rel} h h' :: left')
          (s :: right')
        )
(++) {n = ((4 + n) + n)} (Prick h s h≤s) (Imbalanced {l=l'} {r=r'} h' h'≤l' h'≤r' left' right') =
      rewrite solveNat [n] (1 + ((0 +. n) +. n)) ((0 +. n) + (0 + (1 +. n))) in
        (Imbalanced
          (actualMin {rel} h h')
          (smallerLessThanMin {rel} (minCommutes {rel} \=> (minLessThanGreater {rel} h'≤l')) (min≤max {rel}))
          (congMin {rel} h≤s h'≤r')
          (max' {rel} h h' :: left')
          (s :: right')
        )
(++) {m=3+(m+m)} L@(Balanced h h≤l h≤r left right) [] = rewrite solveNat [m] (((0 +. m) +. m) + 0) ((0 +. m) +. m) in L
(++) {m=3+(m+m)} (Balanced {l} {r} h h≤l h≤r left right) (Singleton h') =
      rewrite solveNat [m] (3 + ((0 + (m .+. m)) + 1)) (4 + (0 + (m .+. m))) in
        (Imbalanced
          (actualMin {rel} h h')
          (smallerLessThanMin {rel} (minLessThanGreater {rel} h≤l) (min≤max {rel}))
          (minLessThanGreater {rel} h≤r)
          (max' {rel} h h' :: left)
          right
        )
(++) {m=3+(m+m)} (Balanced {l} {r} h h≤l h≤r left right) (Prick h' s' h'≤s') =
      rewrite solveNat [m] (3 + ((m .+. m) + 2)) (4 + (m .+ (1 +. m))) in
        (Balanced
          (actualMin {rel} h h')
          (smallerLessThanMin {rel} (minLessThanGreater {rel} h≤l) (min≤max {rel}))
          (congMin {rel} h≤r h'≤s' \=> minCommutes {rel})
          (max' {rel} h h' :: left)
          (s' :: right)
        )
(++) {m=3+(m+m)} {n=3+(m'+m')} (Balanced {l} {r} h h≤l h≤r left right) (Balanced {l=l'} {r=r'} h' h'≤l' h'≤r' left' right') =
      rewrite solveNat [m,m'] (3 + ((m .+. m) + (3 + (m' .+. m')))) (4 + ( (m .+ (1 +. m')) + (m .+ (1 +. m')))) in
        (Imbalanced
          (actualMin {rel} h h')
          (smallerLessThanMin {rel} (congMin {rel} h≤l h'≤l') (min≤max {rel}))
          (congMin {rel} h≤r h'≤r')
          (max' {rel} h h' :: (left ++ left'))
          (right ++ right')
        )
(++) {m=3+(m+m)} {n=4+(m'+m')} (Balanced {l} {r} h h≤l h≤r left right) (Imbalanced {l=l'} {r=r'} h' h'≤l' h'≤r' left' right') =
      rewrite solveNat [m,m'] (3 + ((m .+. m) + (4 + (m' .+. m')))) (4 + ( (m .+ (1 +. m')) + (1 + (m .+ (1 +. m'))))) in
        (Balanced
          (actualMin {rel} h h')
          (congMin {rel} h≤l h'≤l')
          (smallerLessThanMin {rel} (congMin {rel} h≤r h'≤r') (min≤max {rel}))
          (rewrite solveNat [m,m'] (1 + ((0 +. m) + (1 +. m'))) ((0 +. m) + (2 +. m')) in left++left')
          (max' {rel} h h' :: (right ++ right'))
        )
(++) {m=4+m+m} L@(Imbalanced h h≤l h≤r left right) [] = rewrite (plusZeroLeftNeutral m) in rewrite (plusZeroRightNeutral (m+m)) in L
(++) {m=4+m+m} (Imbalanced h h≤l h≤r left right) (Singleton h') =
      rewrite solveNat [m] (((0 +. m) +. m) + 1) ((0 +. m) + (1 +. m)) in
        (Balanced
          (actualMin {rel} h h')
          (minLessThanGreater {rel} h≤l)
          (smallerLessThanMin {rel} (minLessThanGreater {rel} h≤r) (min≤max {rel}))
          left
          (max' {rel} h h' :: right)
        )
(++) {m=4+m+m} (Imbalanced h h≤l h≤r left right) (Prick h' s' h'≤s') =
      rewrite solveNat [m] (((0 +. m) +. m) + 2) (1 + ((0 +. m) + (0 + (1 +. m)))) in
        (Imbalanced
          (actualMin {rel} h h')
          (smallerLessThanMin {rel} (minLessThanGreater {rel} h≤l) (min≤max {rel}))
          (minCommutes {rel} \=> congMin {rel} h'≤s' h≤r)
          (max' {rel} h h' :: left)
          (s' :: right)
        )
(++) {m=4+m+m} {n=3+m'+m'} (Imbalanced h h≤l h≤r left right) (Balanced h' h'≤l' h'≤r' left' right') =
      rewrite solveNat [m,m'] (4 + ((m .+. m) + (3 + (m' .+. m')))) (4 + ( (m .+ (1 +. m')) + (1 + (m .+ (1 +. m'))))) in
        (Balanced
          (actualMin {rel} h h')
          (congMin {rel} h≤l h'≤l')
          (smallerLessThanMin {rel} (congMin {rel} h≤r h'≤r') (min≤max {rel}))
          (left ++ left')
          (max' {rel} h h' :: (right ++ right'))
        )
(++) {m=4+m+m} {n=4+m'+m'} (Imbalanced h h≤l h≤r left right) (Imbalanced h' h'≤l' h'≤r' left' right') =
      rewrite solveNat [m,m'] (((0 +. m) +. m) + (1 + ((3 +. m') +. m'))) (1 + (((0 +. m) + (1 +. m')) + ((1 +. m) + (1 +. m')))) in
        (Imbalanced
            (actualMin {rel} h h')
            (congMin {rel} h≤l h'≤l')
            (smallerLessThanMin {rel} (congMin {rel} h≤r h'≤r') (min≤max {rel}))
            (rewrite solveNat [m,m'] (1 + ((0 +. m) + (1 +. m'))) ((0 +. m) + (2 +. m')) in left ++ left')
            (max' {rel} h h' :: right ++ right')
          )

public export
cnt : DecEq a => LinearOrder a rel => (x: a) -> (xs: Heap {rel} n h) -> Nat
cnt x [] = 0
cnt x (Singleton h) with (decEq x h)
  cnt x (Singleton x) | (Yes Refl) = 1
  cnt x (Singleton h) | (No _) = 0
cnt x (Prick h s hs) with (decEq x h)
  cnt x (Prick x s hs) | (Yes Refl) with (decEq x s)
    cnt x (Prick x x hs) | (Yes Refl) | (Yes Refl) = 2
    cnt x (Prick x s hs) | (Yes Refl) | (No _) = 1
  cnt x (Prick h s hs) | (No _) with (decEq x s)
    cnt x (Prick h x hs) | (No _) | (Yes Refl) = 1
    cnt x (Prick h s hs) | (No _) | (No _) = 0
cnt x (Balanced h {l} {r} hl hr left right) with (decEq x h)
  cnt x (Balanced x {l} {r} x≤l x≤r left right) | (Yes Refl) = 1 + cnt x left + cnt x right
  cnt x (Balanced h {l} {r} h≤l h≤r left right) | (No x≠h) with (connex {rel} x≠h)
    cnt x (Balanced h h≤l h≤r left right) | (No x≠h) | (Left x≤h) = 0
    cnt x (Balanced h h≤l h≤r left right) | (No x≠h) | (Right h≤x) = cnt x left + cnt x right
cnt x (Imbalanced h hl hr left right)  with (decEq x h)
  cnt x (Imbalanced x x≤l x≤r left right) | (Yes Refl) = 1 + cnt x left + cnt x right
  cnt x (Imbalanced h hl hr left right) | (No x≠h) with (connex {rel} x≠h)
    cnt x (Imbalanced h hl hr left right) | (No x≠h) | (Left _) = 0
    cnt x (Imbalanced h hl hr left right) | (No x≠h) | (Right _) = cnt x left + cnt x right

public export
0 strict : DecEq a => LinearOrder a rel  => (x≠h: (x=h -> Void)) -> (x≤h: rel x h) -> (h≤s: rel h s) -> x=s -> Void
strict x≠h x≤h h≤s Refl = void $ x≠h (antisymmetric x≤h h≤s)

public export
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

0 ConsAddsOne': DecEq a => LinearOrder a rel => (0 xs: Heap n h) -> forall x. (1 + cnt {rel} {n} x xs) = cnt {rel} {n=S n} x (Heap.(::) {rel} x xs)
ConsAddsOne' {h} xs with (wellFounded {rel=LT} n)
  ConsAddsOne' {h=()} [] | (Access acc) = rewrite decEqSelfIsYes {x} in Refl
  ConsAddsOne' {h} (Singleton h) | (Access acc) with (decEq x h)
    ConsAddsOne' {h} (Singleton h) | (Access acc) | (Yes Refl) =
      rewrite decEqSelfIsYes {x=h} in
      rewrite decEqSelfIsYes {x=h} in Refl
    ConsAddsOne' {h} (Singleton h) | (Access acc) | (No x≠h) with (connex {rel} x≠h)
      ConsAddsOne' {h} (Singleton h) | (Access acc) | (No x≠h) | (Left x≤h) =
        rewrite decEqSelfIsYes {x} in
        rewrite (decEqContraIsNo x≠h).snd in Refl
      ConsAddsOne' {h} (Singleton h) | (Access acc) | (No x≠h) | (Right h≤x) =
        rewrite (decEqContraIsNo x≠h).snd in
        rewrite decEqSelfIsYes {x} in Refl
  ConsAddsOne' {h} (Prick h s h≤s) | (Access acc) with (decEq x h)
    ConsAddsOne' {h} (Prick h s h≤s) | (Access acc) | (Yes Refl) with (decEq h s)
      ConsAddsOne' {h} (Prick s s h≤s) | (Access acc) | (Yes Refl) | (Yes Refl) =
        rewrite decEqSelfIsYes {x=s} in rewrite decEqSelfIsYes {x=s} in Refl
      ConsAddsOne' {h} (Prick h s h≤s) | (Access acc) | (Yes Refl) | (No h≠s) =
        rewrite decEqSelfIsYes {x=h} in
        rewrite decEqSelfIsYes {x=h} in
        rewrite (decEqContraIsNo h≠s).snd in Refl
    ConsAddsOne' {h} (Prick h s h≤s) | (Access acc) | (No x≠h) with (decEq x s)
      ConsAddsOne' {h} (Prick h s h≤s) | (Access acc) | (No s≠h) | (Yes Refl) =
        let (h≤s ** connex_h≤s) = connexRelIsRight s≠h h≤s in rewrite connex_h≤s in
        let (s≠h ** decno) = decEqContraIsNo $ negEqSym s≠h in rewrite decno in 
        let (h≤s ** connex_h≤s) = connexRelIsLeft s≠h h≤s in rewrite connex_h≤s in
        let (s≠h ** decno) = decEqContraIsNo $ negEqSym s≠h in rewrite decno in 
        let (h≤s ** connex_h≤s) = connexRelIsRight s≠h h≤s in rewrite connex_h≤s in
        rewrite decEqSelfIsYes {x=s} in Refl
      ConsAddsOne' {h} (Prick h s h≤s) | (Access acc) | (No x≠h) | (No x≠s) with (connex {rel} x≠h)
        ConsAddsOne' {h} (Prick h s h≤s) | (Access acc) | (No x≠h) | (No x≠s) | (Left x≤h) =
          rewrite decEqSelfIsYes {x} in rewrite (decEqContraIsNo x≠h).snd in rewrite (decEqContraIsNo x≠s).snd in Refl
        ConsAddsOne' {h} (Prick h s h≤s) | (Access acc) | (No x≠h) | (No x≠s) | (Right h≤x) =
          let (h≠x ** decno) = decEqContraIsNo $ negEqSym x≠h in rewrite decno in
          let (x≠h ** decno) = decEqContraIsNo x≠h in rewrite decno in
          let (h≤x ** connex_h≤x) = connexRelIsLeft h≠x h≤x in rewrite connex_h≤x in
          let (h≤x ** connex_h≤x) = connexRelIsRight x≠h h≤x in rewrite connex_h≤x in
          rewrite decEqSelfIsYes {x} in rewrite (decEqContraIsNo x≠s).snd in Refl
  ConsAddsOne' {h} (Balanced h h≤l h≤r left right) | (Access acc) with (decEq x h)
    ConsAddsOne' {h} (Balanced h h≤l h≤r left right) | (Access acc) | (Yes Refl) =
      rewrite decEqSelfIsYes {x=h} in
      cong (\l => S(l + cnt h right))
        (ConsAddsOne' left | acc _ (LTESucc (LTESucc (lteSuccRight $ lteAddRight _))))
    ConsAddsOne' {h} (Balanced h h≤l h≤r left right) | (Access acc) | (No x≠h) with (connex {rel} x≠h)
      ConsAddsOne' {h} (Balanced h h≤l h≤r left right) | (Access acc) | (No x≠h) | (Left x≤h) =
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
        cong (+ (cnt x right)) (ConsAddsOne' left | acc _ (LTESucc (LTESucc (lteSuccRight $ lteAddRight _))))
  ConsAddsOne' {h} (Imbalanced h h≤l h≤r left right) | (Access acc) with (decEq x h)
    ConsAddsOne' {h} (Imbalanced h h≤l h≤r left right) | (Access acc) | (Yes Refl) =
      rewrite decEqSelfIsYes {x=h} in
      cong S ((plusSuccRightSucc _ _) \=> cong (cnt h left +) (ConsAddsOne' right | acc _ (LTESucc (LTESucc (lteSuccRight $ lteSuccRight $ lteAddRight _)))))
    ConsAddsOne' {h} (Imbalanced h h≤l h≤r left right) | (Access acc) | (No x≠h) with (connex {rel} x≠h)
      ConsAddsOne' {h} (Imbalanced h h≤l h≤r left right) | (Access acc) | (No x≠h) | (Left x≤h) =
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
        plusSuccRightSucc _ _ \=> cong (cnt x left +) (ConsAddsOne' right | acc _ (LTESucc (LTESucc (lteSuccRight $ lteSuccRight $ lteAddRight _))))

public export
ConsAddsOne: DecEq a => LinearOrder a rel => (0 x: a) -> (0 xs: Heap n h) -> (1 + cnt {rel} {n} x xs) = cnt {rel} {n=S n} x (Heap.(::) {rel} x xs)
ConsAddsOne x xs = rewrite ConsAddsOne' xs {x} in Refl
