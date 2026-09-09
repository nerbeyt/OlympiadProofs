import Mathlib.Tactic

-- ADA University Olympiad, Problem 6
-- Box has 10 red, 8 blue, 8 green, 4 yellow balls. Balls are drawn in the
-- dark and set aside one at a time. What is the minimum number of balls
-- we must draw to be sure we have at least two balls of each colour?
-- Claim: the answer is 28.

-- Part 1: drawing 28 or more balls (respecting the per-colour maxima)
-- ALWAYS yields at least two of each colour.
theorem balls_28_suffices (a b c d : ℕ)
    (ha : a ≤ 10) (hb : b ≤ 8) (hc : c ≤ 8) (hd : d ≤ 4)
    (hsum : a + b + c + d ≥ 28) :
    a ≥ 2 ∧ b ≥ 2 ∧ c ≥ 2 ∧ d ≥ 2 := by
  omega

-- Part 2: 27 balls do NOT suffice — exhibit a draw of 27 balls
-- (all red, all blue, all green, one yellow) missing the property.
theorem balls_27_insufficient :
    ∃ a b c d : ℕ, a ≤ 10 ∧ b ≤ 8 ∧ c ≤ 8 ∧ d ≤ 4 ∧
      a + b + c + d = 27 ∧ ¬(a ≥ 2 ∧ b ≥ 2 ∧ c ≥ 2 ∧ d ≥ 2) := by
  refine ⟨10, 8, 8, 1, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem answer_is_28 :
    (∀ a b c d : ℕ, a ≤ 10 → b ≤ 8 → c ≤ 8 → d ≤ 4 → a+b+c+d ≥ 28 →
      a ≥ 2 ∧ b ≥ 2 ∧ c ≥ 2 ∧ d ≥ 2) ∧
    (∃ a b c d : ℕ, a ≤ 10 ∧ b ≤ 8 ∧ c ≤ 8 ∧ d ≤ 4 ∧
      a + b + c + d = 27 ∧ ¬(a ≥ 2 ∧ b ≥ 2 ∧ c ≥ 2 ∧ d ≥ 2)) :=
  ⟨fun a b c d ha hb hc hd hsum => balls_28_suffices a b c d ha hb hc hd hsum,
   balls_27_insufficient⟩
