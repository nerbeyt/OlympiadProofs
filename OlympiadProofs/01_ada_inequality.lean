import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- ADA University Olympiad, Problem 3 (Rafael Alizada)
-- Prove that if B > 0 and x >= 1 then:
-- 1 + 1/B >= (1 + 1/(3B)) * (1 + 1/(3B + x))
theorem ada_ineq (B x : ℝ) (hB : B > 0) (hx : x ≥ 1) :
    1 + 1 / B ≥ (1 + 1 / (3 * B)) * (1 + 1 / (3 * B + x)) := by
  have h3B : (3 * B) > 0 := by linarith
  have h3Bx : (3 * B + x) > 0 := by linarith
  have key : 1 + 1 / B - (1 + 1 / (3 * B)) * (1 + 1 / (3 * B + x))
      = (3 * B + 2 * x - 1) / (3 * B * (3 * B + x)) := by
    field_simp
    ring
  have hnonneg : (3 * B + 2 * x - 1) / (3 * B * (3 * B + x)) ≥ 0 := by
    apply div_nonneg
    · linarith
    · positivity
  linarith [key, hnonneg]
