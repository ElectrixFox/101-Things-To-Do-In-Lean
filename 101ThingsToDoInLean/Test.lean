import Mathlib.Tactic

example : 1 + 1 = 2 := by
  ring

lemma corl1 (a b : ℤ) (hb : b ≠ 0) : Nonempty {y : ℤ | ∃ x : ℤ, y = a - x * b ∧ y ≥ 0} := by
  sorry

lemma corl2 (a b : ℤ) (hb : b ≠ 0) : ∃ (q : ℤ), a - q * b < b := by
  sorry

theorem div_alg (a b : ℤ) (hb : b > 0) : ∃! q : ℤ, ∃! r : ℤ, a = b * q + r ∧ (0 ≤ r ∧ r < b) := by
  have h1 := corl1
  have h2 := corl2
  specialize_all a
  specialize_all b
  have : b > 0 → b ≠ 0 := by
    by_contra
    simp at this
    linarith

  apply this at h1

  sorry
