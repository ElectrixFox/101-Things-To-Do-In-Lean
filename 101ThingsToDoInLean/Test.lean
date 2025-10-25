import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

class MyRing (R : Type) where
  add : R → R → R
  mul : R → R → R
  zero : R
  one : R
  neg : R → R

  add_assoc : ∀ a b c : R, add (add a b) c = add a (add b c)
  add_comm : ∀ a b : R, add a b = add b a
  add_zero : ∀ a : R, add a zero = a
  add_neg : ∀ a : R, add a (neg a) = zero

  mul_assoc : ∀ a b c : R, mul (mul a b) c = mul a (mul b c)
  mul_one : ∀ a : R, mul a one = a
  one_mul : ∀ a : R, mul one a = a

  left_distrib : ∀ a b c : R, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c : R, mul (add a b) c = add (mul a c) (mul b c)


structure MySubring (R : Type) [MyRing R] where
  carrier : Set R
  zero_mem : carrier MyRing.zero
  one_mem : carrier MyRing.one
  add_closed : ∀ {a b : R}, carrier a → carrier b → carrier (MyRing.add a b)
  mul_closed : ∀ {a b : R}, carrier a → carrier b → carrier (MyRing.mul a b)
  neg_closed : ∀ {a : R}, carrier a → carrier (MyRing.neg a)


class MyField (F : Type) extends MyRing F where
  mul_comm : ∀ a b : F, mul a b = mul b a
  one_ne_zero : one ≠ zero
  inv : F → F
  mul_inv_cancel : ∀ a : F, a ≠ zero → mul a (inv a) = one

theorem well_ordering_principle (S : Set ℕ) (hS : S.Nonempty) : ∃ m ∈ S, ∀ n ∈ S, m ≤ n := by
  sorry

lemma div_alg (a b : ℤ) (hb : b ≠ 0) : ∃ q r : ℤ, a = q * b + r ∧ 0 ≤ r ∧ r < Nat.abs b := by

  sorry
