module Main

import Sorted
import Data.Vect
import Data.Nat
import Decidable.Equality

nat0to3 : (Vect 4 Nat) # (Sorted {rel = LTE})
nat0to3 = [0, 1, 2, 3] # (SeveralAreSorted LTEZero (SeveralAreSorted (LTESucc LTEZero) (SeveralAreSorted (LTESucc (LTESucc LTEZero)) (SingletonIsSorted))))

nat4to6 : (Vect 3 Nat) # (Sorted {rel = LTE})
nat4to6 = [4, 5, 6] # (SeveralAreSorted (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))) (SeveralAreSorted (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))) (SingletonIsSorted)))

nat0to6 : (Vect 7 Nat) # (Sorted {rel = LTE})
nat0to6 = subject $ merge {rel=LTE} nat0to3 nat4to6

main : IO ()
main = do
    putStrLn $ show $ let (v # _) = nat0to6 in v
    putStrLn $ show $ let (v # _) = mergeSort {rel=LTE} [7, 2, 3, 8, 5] in v
