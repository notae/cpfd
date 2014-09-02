{-|
Module      : Control.CPFD.Example.Sudokku
Description : Sudoku Example for CPFD
Copyright   : (c) notae@me.com, 2014
License     : BSD-style
Maintainer  : notae@me.com
Stability   : experimental
Portability : POSIX

Originally from:
  <http://overtond.blogspot.jp/2008/07/haskell-sudoku-solver-using-finite.html>
-}

module Control.CPFD.Example.Sudoku where

import Control.CPFD
import Control.Monad (when)
import Control.Monad (zipWithM_)
import Data.List (transpose)

type Puzzle = [Int]

test :: Puzzle
test = [
    0, 0, 0, 0, 8, 0, 0, 0, 0,
    0, 0, 0, 1, 0, 6, 5, 0, 7,
    4, 0, 2, 7, 0, 0, 0, 0, 0,
    0, 8, 0, 3, 0, 0, 1, 0, 0,
    0, 0, 3, 0, 0, 0, 8, 0, 0,
    0, 0, 5, 0, 0, 9, 0, 7, 0,
    0, 5, 0, 0, 0, 8, 0, 0, 6,
    3, 0, 1, 2, 0, 4, 0, 0, 0,
    0, 0, 6, 0, 1, 0, 0, 0, 0 ]

displayPuzzle :: Puzzle -> String
displayPuzzle = unlines . map show . chunk 9

{-|
>>> printSudoku test
[5,6,7,4,8,3,2,9,1]
[9,3,8,1,2,6,5,4,7]
[4,1,2,7,9,5,3,6,8]
[6,8,9,3,7,2,1,5,4]
[7,4,3,6,5,1,8,2,9]
[1,2,5,8,4,9,6,7,3]
[2,5,4,9,3,8,7,1,6]
[3,7,1,2,6,4,9,8,5]
[8,9,6,5,1,7,4,3,2]
<BLANKLINE>
-}
printSudoku :: Puzzle -> IO ()
printSudoku = putStr . unlines . map displayPuzzle . solveSudoku

chunk :: Int -> [a] -> [[a]]
chunk _ [] = []
chunk n xs = ys : chunk n zs where
    (ys, zs) = splitAt n xs

solveSudoku :: Puzzle -> [Puzzle]
solveSudoku puzzle = runFD $ sudoku puzzle

sudoku :: Puzzle -> FD s [Puzzle]
sudoku puzzle = do
  vars <- newNL 81 [1..9]
  zipWithM_ (\x n -> when (n > 0) $ setS x n >> return ()) vars puzzle
  mapM_ alldiff (rows vars)
  mapM_ alldiff (columns vars)
  mapM_ alldiff (boxes vars)
  labelT vars

rows, columns, boxes :: [a] -> [[a]]
rows = chunk 9
columns = transpose . rows
boxes = concat . map (map concat . transpose) . chunk 3 . chunk 3 . chunk 3
