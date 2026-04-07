import Mathlib.Tactic

example : 1 + 1 = 2 := by
  ring

lemma neg_mul_pos_le_self (a b : ℤ) (ha : a < 0) : a * b ≤ a ↔ b > 0 := by
  constructor
  repeat'
  · intro h
    nlinarith

lemma corl1 (a b : ℤ) (hb : b ≠ 0) : Nonempty {y : ℤ | ∃ x : ℤ, y = a - x * b ∧ y ≥ 0} := by
  set A := {y : ℤ | ∃ x : ℤ, y = a - x * b ∧ y ≥ 0}
  rw [A.nonempty_coe_sort, A.nonempty_def]
  unfold A
  simp
  have b_pos : b ^ 2 > 0 := by positivity
  by_cases h : a < 0
  · -- a < 0
    use (a * b)
    ring_nf
    rw [neg_mul_pos_le_self _ _ h]
    exact b_pos
  · -- a ≥ 0
    use -b
    linarith

lemma corl2 (a b : ℤ) (hb : b ≠ 0) : ∃ (q : ℤ), a - q * b < b := by
  sorry

theorem div_alg (a b : ℤ) (hb : b > 0) : ∃ q r : ℤ, a = b * q + r ∧ (0 ≤ r ∧ r < b) := by
  have h1 := corl1
  have h2 := corl2
  specialize_all a
  specialize_all b
  have : b > 0 → b ≠ 0 := by bound
  apply this at hb
  clear this
  simp [hb] at h1 h2
  obtain ⟨r, h1⟩ := h1
  obtain ⟨q, h2⟩ := h2
  use q, r
  constructor
  .
    sorry
  . constructor
    . sorry
    . sorry
