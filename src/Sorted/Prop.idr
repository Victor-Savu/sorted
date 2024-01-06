module Sorted.Prop

import Data.Nat
import Data.Nat.Views

%default total

namespace Prop
    ||| Prop is a dependent pair where the dependent has quantity 0. The dependent can be thought of as a compile-time property of the first element.
    public export
    data Prop: (a: Type) -> (a -> Type) -> Type where
        (#): (f: a) -> (0 prf: p f) -> Prop a p

||| An alternative notation for Prop
public export
(#) : (a: Type) -> (a-> Type) -> Type
(#) a f = Prop a f
