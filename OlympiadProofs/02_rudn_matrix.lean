import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic

-- RUDN Math Olymp 2025, Problem 2 (verification of the worked example)
-- A^r denotes rotation of matrix A by 90 degrees counterclockwise, defined entrywise.
-- The example given: for A = [[1,2,3],[4,5,6],[7,8,9]],
-- A^r = [[3,6,9],[2,5,8],[1,4,7]]
def rot90 (A : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  fun i j => A j (2 - i)

def A : Matrix (Fin 3) (Fin 3) ℤ := !![1,2,3; 4,5,6; 7,8,9]

example : rot90 A = !![3,6,9; 2,5,8; 1,4,7] := by
  decide
