import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

-- RUDN Math Olymp 2025, Problem 1 (Set Theory / Zulip set)
-- 10 cells arranged in a circle, each holds a digit 0 or 1.
-- From a starting cell C, repeatedly move to one of the two neighboring
-- cells and append that cell's digit to a string S (10 steps total).
-- Question: how many colorings of the 10 cells make it possible, FROM
-- EVERY STARTING CELL, to produce S = 0101010101 by some choice of moves?

def stepCell (c : Fin 10) (dir : Bool) : Fin 10 := if dir then c + 1 else c - 1

def walk (col : Fin 10 → Bool) (dirs : ℕ → Bool) : ℕ → Fin 10 → (Fin 10 × List Bool)
  | 0, c0 => (c0, [])
  | (k+1), c0 =>
      let (c, l) := walk col dirs k c0
      let c' := stepCell c (dirs k)
      (c', l ++ [col c'])

def target : List Bool := [false, true, false, true, false, true, false, true, false, true]

def dirsFromFin (dirs : Fin 10 → Bool) : ℕ → Bool :=
  fun i => if h : i < 10 then dirs ⟨i, h⟩ else false

def possibleFrom (col : Fin 10 → Bool) (c0 : Fin 10) : Bool :=
  decide (∃ dirs : Fin 10 → Bool, (walk col (dirsFromFin dirs) 10 c0).2 = target)

def possibleFromAll (col : Fin 10 → Bool) : Bool :=
  decide (∀ c0 : Fin 10, possibleFrom col c0 = true)

def countGood : ℕ :=
  (Finset.univ.filter (fun col : Fin 10 → Bool => possibleFromAll col = true)).card

#eval countGood

theorem countGood_eq_10 : countGood = 10 := by native_decide
