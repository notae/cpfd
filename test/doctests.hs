module Main where

import Test.DocTest

main :: IO ()
main = doctest [ "src/Control/CPFD.hs"
               , "src/Control/CPFD/Crisp.hs"
               , "src/Control/CPFD/Crisp/Solver.hs"
               , "src/Control/CPFD/Crisp/Primitives.hs"
               , "src/Control/CPFD/Internal/Queue.hs"
               , "src/Control/CPFD/Example/Example.hs"
               , "src/Control/CPFD/Example/Sudoku.hs"
               , "src/Control/CPFD/Example/Fuzzy.hs"
               , "src/Control/CPFD/Fuzzy.hs"
               , "src/Control/CPFD/Fuzzy/Solver.hs"
               , "src/Control/CPFD/Fuzzy/Solver2.hs"
               , "src/Control/CPFD/Fuzzy/Primitives.hs"
               , "src/Data/Container.hs"
               , "src/Data/Domain.hs"
               , "src/Data/Fuzzy.hs" ]
