module Main

import Sorted.MergeSort
import Sorted.InsertionSort
import Sorted.Container.List
import Data.Nat
import Sorted.Prop

main : IO ()
main = do
    putStrLn $ show $ let (v # _) = mergeSort {rel=LTE} [7, 2, 3, 8, 5] in v
    putStrLn $ show $ let (v # _) = insertionSort {rel=LTE} [7, 2, 3, 8, 5] in v
