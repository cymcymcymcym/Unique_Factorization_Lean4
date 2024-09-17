import UFT.Axioms
import UFT.RingResults
import UFT.OrderedRingResults
import UFT.IntegralDomain
import UFT.Division
import UFT.GCD

def prime {α : Type} (R : WellOrderedRing α) (p : α) : Prop :=
  R.gt R.one p ∧ ∀ a b : α, R.mul a b = p → (R.gt R.zero a) → (R.gt R.zero b) → a = R.one ∨ b = R.one

def composite {α : Type} (R : WellOrderedRing α) (n : α) : Prop :=
  R.gt R.one n ∧ ¬(prime R n)

def coprime {α : Type} (R : WellOrderedRing α) (a b : α) : Prop :=
  is_gcd R R.one a b

lemma atleast2divisors {α : Type} (R : WellOrderedRing α) (a : α) (h : R.gt R.one a) : ∃ x y : α, y ≠ x ∧ (R.mul x y = a) := by
  use a, R.one
  apply And.intro
  · have h1 : R.one ≠ a := by
      apply gt_implies_neq R.tomyOrderedRing R.one a h
    exact h1
  · exact R.mul_ident a

lemma composite_more_than_2_divisors {α : Type} (R : WellOrderedRing α) (a : α) (h : composite R a) : ∃ x y : α, x ≠ R.one ∧ y ≠ R.one ∧ x ≠ a ∧ y ≠ a ∧ R.mul x y = a := by
  rcases h with ⟨h1, h2⟩
  have ha_neq0 : a ≠ R.zero := by
      intro h
      rw [h] at h1
      have h1' : R.neg R.one ∈ R.P := by
        unfold myOrderedRing.gt at h1
        rw [R.add_comm] at h1
        rw [R.add_zero] at h1
        exact h1
      apply neg_one_not_pos R.tomyOrderedRing h1'
  have h3 : ∃ x y : α, R.mul x y = a ∧ x ≠ R.one ∧ y ≠ R.one := by
    by_contra H
    push_neg at H
    have h4 : prime R a := by
      constructor
      · exact h1
      · intros x y hxy
        specialize H x y
        tauto
    contradiction
  rcases h3 with ⟨x, y, hxy, hx1, hy1⟩
  use x, y
  constructor
  · exact hx1
  constructor
  · exact hy1
  constructor
  · intro hxa
    rw [hxa, R.mul_comm] at hxy
    have hxy' : R.mul a y = a := by
      rw [R.mul_comm]
      exact hxy
    have hy1' : y = R.one := by
      apply local_identity_one_in_int_dom R.tomyRing a y hxy' ha_neq0
      exact ordered_ring_is_integral_domain R.tomyOrderedRing
    contradiction
  constructor
  · intro hya
    rw [hya] at hxy
    have hxy' : R.mul a x = a := by
      rw [R.mul_comm]
      exact hxy
    have hx1' : x = R.one := by
      apply local_identity_one_in_int_dom R.tomyRing a x hxy' ha_neq0
      exact ordered_ring_is_integral_domain R.tomyOrderedRing
    contradiction
  exact hxy

  -- tbc
