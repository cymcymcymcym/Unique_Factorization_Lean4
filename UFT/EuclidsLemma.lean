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

lemma gt0_neq1_implies_gt1 {α : Type} (R : WellOrderedRing α) (a : α) (h : R.gt R.zero a) (h1 : a ≠ R.one) : R.gt R.one a := by
  unfold myOrderedRing.gt at h
  rw [inv_zero_eq_zero] at h
  rw [R.add_zero] at h
  have a_trich := lt_eq_gt R.tomyOrderedRing a R.one
  rcases a_trich with (a_lt_one | a_eq_one | a_gt_one)
  · rcases a_lt_one with ⟨in_use, tmp11, tmp12⟩
    exact lt_rev_gt R.tomyOrderedRing a R.one in_use
  · rcases a_eq_one with ⟨tmp21, in_use, tmp22⟩
    contradiction
  · rcases a_gt_one with ⟨tmp31, tmp32, in_use⟩
    have one_lt_a := gt_rev_lt R.tomyOrderedRing a R.one in_use
    have a_trich2 := lt_eq_gt R.tomyOrderedRing R.zero a
    rcases a_trich2 with (a_lt_zero | a_eq_zero | a_gt_zero)
    · rcases a_lt_zero with ⟨in_use, tmp41, tmp42⟩
      unfold myOrderedRing.lt at in_use
      rw [R.add_comm] at in_use
      rw [R.add_zero] at in_use
      have neg_a_not_pos := R.trichotomy2 a h
      contradiction
    · rcases a_eq_zero with ⟨in_use, tmp51, tmp52⟩
      have zero_pos : R.zero ∈ R.P := by
        rw [tmp51]
        exact h
      have zero_npos : R.zero ∉ R.P := R.trichotomy1
      contradiction
    · rcases a_gt_zero with ⟨tmp61, tmp62, in_use⟩
      have nibzo' := nibzo R
      have exist_gt0_lt1 : ∃ n, R.gt R.zero n ∧ R.gt n R.one := by
        use a
      contradiction

lemma unchange_imply_eq1 {α : Type} (R : myOrderedRing α) (a b: α) (h0 : a ≠ R.zero) (h : R.mul a b = a) : b = R.one := by
  have mul_one : R.mul a R.one = a := R.mul_ident a
  rw (config := {occs := .pos [2]}) [←mul_one] at h
  apply ordered_ring_cancellation R a b R.one h0 h

theorem composite_has_positive_div {α : Type} (R : WellOrderedRing α) (a : α) (h : composite R a) : ∃ x y : α, x ≠ R.one ∧ y ≠ R.one ∧ R.mul x y = a ∧ x ∈ R.P := by
  unfold composite at h
  rcases h with ⟨agt1, anprime⟩
  unfold prime at anprime
  simp at anprime
  have pos_div := anprime agt1
  rcases pos_div with ⟨x, y, xy_eq_a, x_gt0, y_gt0, x_n1, y_n1⟩
  have x_pos : x ∈ R.P := gt0_implies_pos R.tomyOrderedRing x x_gt0
  use x, y

theorem have_prime_divisor {α : Type} (R : WellOrderedRing α) :
  ∀ a : α, R.gt R.one a → ∃ p, prime R p ∧ divisible R p a:= by
  intro a a_gt1
  by_contra h
  let S := {x : α | R.gt R.one x ∧ ¬∃ p : α, prime R p ∧ divisible R p x}

  have S_nonempty : ∃ x : α, x ∈ S := by
    use a
    constructor
    exact a_gt1
    exact h

  have S_pos : S ⊆ R.P := by
    intro s hs
    rcases hs with ⟨s_gt1, s_no_prime_factor⟩
    apply gt0_implies_pos R.tomyOrderedRing s
    apply gt_transitive R.tomyOrderedRing s R.one R.zero s_gt1 (one_gt_zero R.tomyOrderedRing)

  have exist_least := R.well_ordered S S_nonempty S_pos
  rcases exist_least with ⟨l, l_in_S, l_least_in_S⟩
  rcases l_in_S with ⟨l_gt1, l_no_prime_factor⟩

  have l_not_prime : ¬ prime R l := by
    intro h_prime
    have l_div_l : divisible R l l := by
      unfold divisible
      use R.one
      rw [R.mul_ident]
    have l_exist_prime_div : ∃ p, prime R p ∧ divisible R p l := by
      use l
    contradiction

  have l_composite : composite R l := by
    unfold composite
    exact ⟨l_gt1, l_not_prime⟩

  have l_divisor := composite_has_positive_div R l l_composite
  rcases l_divisor with ⟨x, y, xn1, yn1, xy_eq_l, x_pos⟩

  have x_no_prime_divisors : ¬∃p, prime R p ∧ divisible R p x := by
    by_contra p_div_x
    rcases p_div_x with ⟨p, p_prime, p_div_x⟩
    rcases p_div_x with ⟨q, qp_eq_x⟩
    rw [←qp_eq_x] at xy_eq_l
    rw [R.mul_assoc] at xy_eq_l
    have p_div_l : divisible R p l := by
      use (R.mul q y)
    have l_has_prime_div : ∃p, prime R p ∧ divisible R p l := by
      use p
    contradiction

  have x_gt0 : R.gt R.zero x := by
    unfold myOrderedRing.gt
    rw [inv_zero_eq_zero]
    rw [R.add_zero]
    exact x_pos

  have x_gt1 : R.gt R.one x := by
    apply gt0_neq1_implies_gt1 R x x_gt0 xn1

  have x_in_S : x ∈ S := by
    exact ⟨x_gt1, x_no_prime_divisors⟩

  have l_le_x : R.le x l := by
    exact l_least_in_S x x_in_S

  have xn0 : x ≠ R.zero := by
    intro x0
    rw [x0] at x_pos
    have zero_npos := R.trichotomy1
    contradiction

  have x_div_l : divisible R x l := by
    use y

  have l_gt0 : R.gt R.zero l := by
    apply gt_transitive R.tomyOrderedRing l R.one R.zero l_gt1 (one_gt_zero R.tomyOrderedRing)

  have x_le_l : R.le l x := by
    apply a_div_b_then_a_leq_b R x l xn0 l_gt0 x_div_l

  have x_eq_l := le_lerev_implies_eq R.tomyOrderedRing x l l_le_x x_le_l

  have y1 : y = R.one := by
    rw [←x_eq_l] at xy_eq_l
    have xmul1 : R.mul x R.one = x := R.mul_ident x
    have muly_eq_mul1 : R.mul x y = R.mul x R.one := by
      rw [xmul1]
      exact xy_eq_l
    exact ordered_ring_cancellation R.tomyOrderedRing x y R.one xn0 muly_eq_mul1

  contradiction

theorem fundamental_lemma {α : Type} (R : WellOrderedRing α) (a b c : α)
  (ha : a ∈ R.P) (hb : b ∈ R.P) (hdiv : divisible R a (R.mul b c)) (hcoprime : coprime R a b) : divisible R a c := by
  unfold divisible
  unfold coprime at hcoprime
  have exist_linear_comp := bezout R a b ha hb
  rcases exist_linear_comp with ⟨x, y, d, d_is_gcd, linear_comb_eq_d⟩
  have d_eq_one := gcd_unique R a b d R.one d_is_gcd hcoprime
  rw [d_eq_one] at linear_comb_eq_d
  have linear_comb_mul_c : R.mul c (R.add (R.mul a x) (R.mul b y)) = R.mul c R.one:= by
    rw [linear_comb_eq_d]
  unfold divisible at hdiv
  rcases hdiv with ⟨q, aqeqbc⟩
  rw [R.distrib] at linear_comb_mul_c
  rw [←R.mul_assoc] at linear_comb_mul_c
  rw [R.mul_comm c a] at linear_comb_mul_c
  rw [R.mul_assoc] at linear_comb_mul_c
  rw [←R.mul_assoc c b y] at linear_comb_mul_c
  rw [R.mul_comm c b] at linear_comb_mul_c
  rw [←aqeqbc] at linear_comb_mul_c
  rw [R.mul_assoc] at linear_comb_mul_c
  rw [←R.distrib] at linear_comb_mul_c
  rw [R.mul_ident] at linear_comb_mul_c
  use (R.add (R.mul c x) (R.mul q y))

theorem euclids_lemma {α : Type} (R : WellOrderedRing α) (a b p : α) (hp : prime R p) (hdiv : divisible R p (R.mul a b)) : (divisible R p a) ∨ (divisible R p b) := by
  by_cases pdiva : divisible R p a
  · left
    exact pdiva
  · sorry
