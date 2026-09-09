import Mathlib.Tactic

-- ICO Advanced/Free Levels Nov 2024, Problem 10 (Bahman's table)
-- Bahman fills an 8x8 table with numbers 1..4 uniformly at random, then
-- picks a random pair 1<=a<b<=4 and colours all cells with value a or b
-- gray. value = 64 * t where t = number of completely-gray rows.
-- What is the average value, over all fillings and all choices of (a,b)?
--
-- For ANY fixed pair (a,b), a single row (8 iid cells uniform on 4 values)
-- is completely gray with probability (2/4)^8 = 1/256, so by linearity of
-- expectation E[t] = 8 * (1/256) = 1/32, independent of which (a,b) was
-- chosen -- hence the overall average is 64 * 1/32 = 2, regardless of how
-- (a,b) is chosen among the 6 possible pairs.

-- Model a single row (8 cells, each in Fin 4) and count how many of the
-- 4^8 = 65536 possible rows are "completely gray" for a FIXED pair (a,b),
-- i.e. every cell lies in {a,b}. We verify this count is exactly 2^8=256
-- for every one of the 6 possible pairs (a,b), confirming the constant
-- per-row probability 256/65536 = 1/256 used in the argument above.

def rowsAllIn (s : Finset (Fin 4)) : Finset (Fin 8 → Fin 4) :=
  Finset.univ.filter (fun row => ∀ i, row i ∈ s)

def allPairs : Finset (Fin 4 × Fin 4) :=
  Finset.univ.filter (fun p => p.1 < p.2)

theorem six_pairs : allPairs.card = 6 := by native_decide

theorem rows_gray_count_constant :
    ∀ p ∈ allPairs, (rowsAllIn {p.1, p.2}).card = 256 := by
  native_decide

-- total rows
theorem total_rows : (Finset.univ : Finset (Fin 8 → Fin 4)).card = 65536 := by
  native_decide

-- Hence for every pair, P(row completely gray) = 256/65536 = 1/256,
-- E[t] = 8 * 1/256 = 1/32, and the average table value is
-- 64 * (1/32) = 2, independent of (a,b), confirming the answer 2.
theorem average_value_is_2 :
    (64 : ℚ) * (8 * (256 / 65536)) = 2 := by norm_num
