import Mathlib.Tactic

example : 1 + 1 = 2 := by
  ring

lemma corl1 (a b : ℤ) (hb : b ≠ 0) : Nonempty {x : ℤ ∣ (a - x * b) ∧ (a - x * b ≥ 0)} := by
  sorry

theorem div_alg (a b : ℤ) (hb : b > 0) : ∃! q : ℤ, ∃! r : ℤ, a = b * q + r ∧ (0 ≤ r ∧ r < b) := by

  sorry
