import UFT.Axioms
import UFT.RingResults
import UFT.OrderedRingResults

def is_zero_divisor {α : Type} (R : myRing α) (a : α) : Prop :=
  a ≠ R.zero ∧ ∃ b : α, b ≠ R.zero ∧ R.mul a b = R.zero

def is_integral_domain_my {α : Type} (R : myRing α) : Prop :=
  ∀ a b : α, R.mul a b = R.zero → a = R.zero ∨ b = R.zero

theorem local_identity_one_in_int_dom {α : Type} (R : myRing α)
  (a b : α) (h : R.mul a b = a) (ha : a ≠ R.zero) (hid : is_integral_domain R) : b = R.one := by
  have h1 : R.sub (R.mul a b) a = R.zero := by
    rw [h]
    unfold myRing.sub
    exact R.add_inv a

  have h1' : R.add (R.mul a b) (R.neg a) = R.zero := by
    exact h1

  have h2 : R.mul a (R.sub b R.one) = R.zero := by
    unfold myRing.sub
    rw [R.distrib]
    rw [R.mul_comm a (R.neg R.one)]
    rw [←inv_eq_mul_neg1]
    exact h1'

  have h3 : R.sub b R.one = R.zero ∨ a = R.zero := by
    apply hid
    rw [R.mul_comm]
    exact h2

  have h4 : R.sub b R.one = R.zero := by
    rcases h3 with h3' | h3'
    · exact h3'
    · contradiction

  have h4' : R.add b (R.neg R.one) = R.zero := by
    exact h4

  apply add_inv_to_zero R b R.one h4'

theorem mult_cancel_in_int_dom {α : Type} (R : myRing α) (a b b' : α)
  (h : R.mul a b = R.mul a b') (ha : a ≠ R.zero) (hid : is_integral_domain_my R) : b = b' := by
  have h1 : R.mul a (R.sub b b') = R.zero := by
    unfold myRing.sub
    rw [R.distrib]
    rw [h]
    rw [R.mul_comm a (R.neg b')]
    rw [←inv_assoc]
    rw [R.mul_comm b' a]
    exact R.add_inv (R.mul a b')

  have h2 : R.sub b b' = R.zero ∨ a = R.zero := by
    apply hid
    rw [R.mul_comm]
    exact h1

  have h3 : R.sub b b' = R.zero := by
    rcases h2 with h2' | h2'
    · exact h2'
    · contradiction

  have h4 : R.add b (R.neg b') = R.zero := by
    exact h3

  exact add_inv_to_zero R b b' h4

lemma neither_pos_nor_neg_imp_zero {α : Type} (R : myOrderedRing α) (a : α) (h1 : ¬(a ∈ R.P) ) (h2 : ¬(R.neg a ∈ R.P)) : a = R.zero := by
  by_cases h_trichotomy : a = R.zero
  · exact h_trichotomy

  have h_trich : a ∈ R.P ∨ R.neg a ∈ R.P := by
    right
    apply R.trichotomy3 a h1 h_trichotomy

  have h_a_neg : R.neg a ∈ R.P := by
    rcases h_trich with h_trich' | h_trich'
    · contradiction
    exact h_trich'

  contradiction

theorem ordered_ring_is_integral_domain {α : Type} (R : myOrderedRing α) : is_integral_domain_my R.tomyRing := by
  unfold is_integral_domain_my
  intros a b h_mul_zero
  by_contra hc
  push_neg at hc
  rcases hc with ⟨ha, hb⟩

  have h_trichotomy : ∀ x : α, x ≠ R.zero → x ∈ R.P ∨ R.neg x ∈ R.P := by
    intro x hx
    by_contra h_not_or
    push_neg at h_not_or
    have h_neg_not_in_P : R.neg x ∉ R.P := by
      intro h_neg_in_P
      exact h_not_or.2 h_neg_in_P
    have h_x_zero : x = R.zero := by
      apply neither_pos_nor_neg_imp_zero R x h_not_or.1 h_neg_not_in_P
    contradiction

  rcases h_trichotomy a ha with ha_pos | ha_neg


  rcases h_trichotomy b hb with hb_pos | hb_neg
  -- Case 1: a ∈ P and b ∈ P
  · have h_pos : R.mul a b ∈ R.P := R.P_mul a b ha_pos hb_pos
    rw [h_mul_zero] at h_pos
    exact R.trichotomy1 h_pos

  -- Case 2: a ∈ P and b ∉ P
  · have h_neg_pos : R.neg (R.mul a b) ∈ R.P := by
      rw [R.mul_comm]
      rw [inv_assoc]
      apply R.P_mul (R.neg b) a hb_neg ha_pos
    rw [h_mul_zero] at h_neg_pos
    have h_zero_pos : R.zero ∈ R.P := by
      rw [← inv_zero_eq_zero]
      exact h_neg_pos
    have h_zero_not_pos : R.zero ∉ R.P := by
      exact R.trichotomy1
    contradiction


  rcases h_trichotomy b hb with hb_pos | hb_neg
  -- Case 3: a ∉ P and b ∈ P
  · have h_neg_pos : R.neg (R.mul a b) ∈ R.P := by
      rw [inv_assoc]
      apply R.P_mul (R.neg a) b ha_neg hb_pos
    rw [h_mul_zero] at h_neg_pos
    have h_zero_pos : R.zero ∈ R.P := by
      rw [← inv_zero_eq_zero]
      exact h_neg_pos
    have h_zero_not_pos : R.zero ∉ R.P := by
      exact R.trichotomy1
    contradiction

  -- Case 4: a ∉ P and b ∉ P
  · have h_mul_neg_neg_pos : R.mul (R.neg a) (R.neg b) ∈ R.P := by
      apply R.P_mul (R.neg a) (R.neg b) ha_neg hb_neg
    have h_mul_neg_neg_eq : R.mul (R.neg a) (R.neg b) = R.mul a b := by
      rw [inv_mul_inv]
    have h_zero_pos : R.zero ∈ R.P := by
      rw [←h_mul_zero]
      rw [←h_mul_neg_neg_eq]
      exact h_mul_neg_neg_pos
    have h_zero_not_pos : R.zero ∉ R.P := by
      exact R.trichotomy1
    contradiction

theorem ordered_ring_cancellation {α : Type} (R : myOrderedRing α) :
  ∀ a b b' : α, a ≠ R.zero → R.mul a b = R.mul a b' → b = b' := by
  intros a b b' ha h
  apply mult_cancel_in_int_dom R.tomyRing a b b' h ha
  apply ordered_ring_is_integral_domain R

lemma unchange_imply_eq1 {α : Type} (R : myOrderedRing α) (a b: α) (h0 : a ≠ R.zero) (h : R.mul a b = a) : b = R.one := by
  have mul_one : R.mul a R.one = a := R.mul_ident a
  rw (config := {occs := .pos [2]}) [←mul_one] at h
  apply ordered_ring_cancellation R a b R.one h0 h

theorem ordered_ring_local_identity {α : Type} (R : myOrderedRing α) :
  ∀ a b : α, R.mul a b = a → a ≠ R.zero → b = R.one := by
  intros a b h ha
  apply local_identity_one_in_int_dom R.tomyRing a b h ha
  apply ordered_ring_is_integral_domain R
