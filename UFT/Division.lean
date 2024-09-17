import UFT.Axioms
import UFT.RingResults
import UFT.OrderedRingResults
import UFT.IntegralDomain

def divisible {α : Type} (R : WellOrderedRing α) (a b : α) : Prop :=
  ∃ k : α, R.mul a k = b

theorem nibzo {α : Type} (R : WellOrderedRing α) : ¬∃ n : α, R.gt R.zero n ∧ R.gt n R.one := by
  by_contra h
  rcases h with ⟨n, h1, h2⟩
  let S := {x : α | R.gt R.zero x ∧ R.gt x R.one}
  have hS : S.Nonempty := by
    use n
    exact ⟨h1, h2⟩
  have hS_subset : S ⊆ R.P := by
    intro x hx
    apply gt0_implies_pos R.tomyOrderedRing
    exact hx.1
  have hS_well_ordered : ∃ m ∈ S, ∀ s ∈ S, R.le s m:= by
    apply R.well_ordered S hS hS_subset
  rcases hS_well_ordered with ⟨m, hm, hm_min⟩
  have m_pos : m ∈ R.P := by
      exact gt0_implies_pos R.tomyOrderedRing m hm.1
  let msq := R.mul m m
  have rw_msq : msq = R.mul m m := by
    rfl
  have msq_pos : msq ∈ R.P := by
    apply R.P_mul m m m_pos m_pos

  have msq_gt0 : R.gt R.zero msq := by
    unfold myOrderedRing.gt
    rw [inv_zero_eq_zero R.tomyRing]
    rw [R.add_zero]
    exact msq_pos

  have msq_lt_m : R.lt m msq := by
    unfold myOrderedRing.lt
    rw [rw_msq]
    rw [inv_assoc]
    rw [R.mul_comm]
    rw (config := {occs := .pos [1]}) [←R.mul_ident m]
    rw [←R.distrib]
    apply R.P_mul
    exact m_pos
    have one_add_neg_m_pos : R.add R.one (R.neg m) ∈ R.P := by
      unfold myOrderedRing.gt at hm
      exact hm.2
    exact one_add_neg_m_pos

  have _1gt_msq : R.gt msq R.one:= by
    apply lt_rev_gt R.tomyOrderedRing R.one msq
    apply lt_transitive R.tomyOrderedRing R.one m msq
    exact gt_rev_lt R.tomyOrderedRing m R.one hm.2
    exact msq_lt_m

  have msq_in_S : msq ∈ S := by
    constructor
    · exact msq_gt0
    · exact _1gt_msq

  have msq_neq_m : msq ≠ m := by
    have m_gt_msq : R.gt msq m := by
      exact lt_rev_gt R.tomyOrderedRing m msq msq_lt_m
    apply gt_implies_neq R.tomyOrderedRing msq m m_gt_msq

  have m_lt_msq : R.lt msq m := by
    have contradiction := hm_min msq msq_in_S
    unfold myOrderedRing.le at contradiction
    rcases contradiction with h | h
    · -- Case 1: R.add msq (R.neg m) ∈ R.P
      unfold myOrderedRing.lt
      exact h
    · -- Case 2: msq = m
      exfalso
      exact msq_neq_m h

  have m_lt_m : R.lt m m := by
    apply lt_transitive R.tomyOrderedRing m msq m
    exact msq_lt_m
    exact m_lt_msq

  exact lt_not_refl R.tomyOrderedRing m m_lt_m

theorem a_div_b_then_a_leq_b {α : Type} (R : WellOrderedRing α) (a b : α)
  (ha : a ≠ R.zero) (hb : R.gt R.zero b) (h_div : divisible R a b) : R.le b a := by
  unfold myOrderedRing.le
  unfold myOrderedRing.gt at hb
  rw [inv_zero_eq_zero] at hb
  rw [R.add_zero] at hb
  rcases h_div with ⟨t, ht⟩
  have a_trich := lt_eq_gt R.tomyOrderedRing a R.zero
  rcases a_trich with (h_a_gt0 | h_a_eq_zero | h_a_lt0)
  · rcases h_a_gt0 with ⟨a_pos, tmp11, tmp12⟩
    unfold myOrderedRing.lt at a_pos
    rw [inv_zero_eq_zero] at a_pos
    rw [R.add_zero] at a_pos
    rw [←ht]
    rw [inv_eq_mul_neg1]
    rw [R.mul_comm (R.neg R.one) a]
    rw [←R.distrib]
    have h_t_pos : R.gt R.zero t := by
      unfold myOrderedRing.gt
      rw [inv_zero_eq_zero]
      rw [R.add_zero]
      have t_trich := lt_eq_gt R.tomyOrderedRing t R.zero
      rcases t_trich with (t_gt0 | t_eq_zero | t_lt0)
      · rcases t_gt0 with ⟨t_pos , tmp1'11, tmp1'12⟩
        unfold myOrderedRing.lt at t_pos
        rw [inv_zero_eq_zero] at t_pos
        rw [R.add_zero] at t_pos
        exact t_pos
      · rcases t_eq_zero with ⟨tmp1'21, t0, t1'22⟩
        have b0 : b = R.zero := by
          rw [←ht]
          rw [t0]
          rw [mul_zero]
        have pos0 : R.zero ∈ R.P := by
          rw [←b0]
          exact hb
        have npos0 := R.trichotomy1
        contradiction
      · rcases t_lt0 with ⟨tmp1'31, tmp1'32, t_neg⟩
        unfold myOrderedRing.gt at t_neg
        rw [R.add_comm] at t_neg
        rw [R.add_zero] at t_neg
        have neg_b_pos : R.neg b ∈ R.P := by
          rw [←ht]
          rw [R.mul_comm]
          rw [inv_assoc]
          exact R.P_mul (R.neg t) a t_neg a_pos
        have neg_b_npos := R.trichotomy2 b hb
        contradiction
    have t_trich2 := lt_eq_gt R.tomyOrderedRing t R.one
    rcases t_trich2 with (t_gt1 | t_eq1 | t_lt1)
    · rcases t_gt1 with ⟨t_gt1' , tmp2'11, tmp2'12⟩
      unfold myOrderedRing.lt at t_gt1'
      left
      exact R.P_mul a (R.add t (R.neg R.one)) a_pos t_gt1'
    · rcases t_eq1 with ⟨tmp2'21, t1, tmp2'22⟩
      right
      rw [t1]
      exact R.mul_ident a
    · rcases t_lt1 with ⟨tmp2'31, tmp2'32, t_lt1'⟩
      have pre_contra := (nibzo R)
      have post_contra : ∃ n, R.gt R.zero n ∧ R.gt n R.one := by
        use t
      contradiction


  · rcases h_a_eq_zero with ⟨tmp21, a0, tmp22⟩
    contradiction

  · rcases h_a_lt0 with ⟨tmp31, tmp32, a_neg⟩
    unfold myOrderedRing.gt at a_neg
    rw [R.add_comm] at a_neg
    rw [R.add_zero] at a_neg
    left
    apply R.P_add b (R.neg a) hb a_neg

def is_valid_division_result {α : Type} (R : WellOrderedRing α) (a b q r : α) : Prop :=
  a ∈ R.P ∧
  b ∈ R.P ∧                -- b > 0
  R.add (R.mul b q) r = a ∧      -- a = bq + r
  R.ge R.zero r ∧                -- r ≥ 0
  R.gt r b                       -- r < b

theorem division_algorithm_existence {α : Type} (R : WellOrderedRing α) (a b : α) (ha : a ∈ R.P) (hb : b ∈ R.P) :
  ∃ q r, is_valid_division_result R a b q r := by
  unfold is_valid_division_result


  let S := { r : α | ∃ q, R.add (R.mul b q) r = a ∧ R.gt R.zero r}

  have S_nonempty : S.Nonempty := by
    use a
    use R.zero
    constructor
    · rw [mul_zero]
      rw [R.add_comm]
      rw [R.add_zero]
    · unfold myOrderedRing.gt
      rw [inv_zero_eq_zero]
      rw [R.add_zero]
      exact ha

  have S_pos : S ⊆ R.P := by
    intro r hr
    rcases hr with ⟨q, hq⟩
    unfold myOrderedRing.gt at hq
    rw [inv_zero_eq_zero] at hq
    rw [R.add_zero] at hq
    exact hq.2

  rcases R.well_ordered S S_nonempty S_pos with ⟨min, min_in_S, min_least⟩
  rcases min_in_S with ⟨q_min, min_eq, min_pos⟩

  have b_trich := lt_eq_gt R.tomyOrderedRing b min
  rcases b_trich with (r_lt_b | r_eq_b | r_gt_b)
  · rcases r_lt_b with ⟨r_lt_b', tmp11, tmp12⟩
    have b_gt_r := lt_rev_gt R.tomyOrderedRing b min r_lt_b'
    use q_min
    use min
    have min_ge_zero : R.ge R.zero min := by
      unfold myOrderedRing.ge
      unfold myOrderedRing.gt at min_pos
      left
      exact min_pos
    exact ⟨ha, hb, min_eq, min_ge_zero, b_gt_r⟩

  · rcases r_eq_b with ⟨tmp21, r_eq_b', tmp22⟩
    let q_final := R.add q_min R.one
    have q_final_rw : q_final = R.add q_min R.one := rfl
    --let r_final := R.zero
    have q_final_eq : R.add (R.mul b q_final) R.zero = a := by
      rw [r_eq_b'] at min_eq
      rw (config := {occs := .pos [2]}) [←(R.mul_ident min)] at min_eq
      rw [←R.distrib] at min_eq
      rw [r_eq_b']
      rw [R.add_zero]
      rw [q_final_rw]
      exact min_eq
    have zero_ge_zero : R.ge R.zero R.zero := by
      unfold myOrderedRing.ge
      right
      rfl
    rw [←r_eq_b'] at min_pos
    use q_final
    use R.zero

  · rcases r_gt_b with ⟨tmp31, tmp32, r_gt_b'⟩
    let min_sub_b := R.add min (R.neg b)
    have min_sub_b_rw : min_sub_b = R.add min (R.neg b) := by rfl
    have min_sub_b_in_S : min_sub_b ∈ S := by
      use R.add q_min R.one
      constructor
      · rw [min_sub_b_rw]
        rw [R.distrib]
        rw [R.mul_ident]
        rw [R.add_assoc]
        rw [R.add_comm min (R.neg b)]
        rw [←R.add_assoc b (R.neg b) min]
        rw [R.add_inv]
        rw [R.add_comm R.zero min]
        rw [R.add_zero]
        exact min_eq
      · -- Prove min - b > 0
        unfold myOrderedRing.gt
        rw [inv_zero_eq_zero]
        rw [R.add_zero]
        rw [min_sub_b_rw]
        unfold myOrderedRing.gt at r_gt_b'
        exact r_gt_b'
    have min_lt_min_sub_b : R.lt min_sub_b min := by
      unfold myOrderedRing.lt
      have min_le_min_sub_b : R.le min_sub_b min := by
        apply min_least min_sub_b min_sub_b_in_S
      unfold myOrderedRing.le at min_le_min_sub_b
      rcases min_le_min_sub_b with (lt' | eq')
      exact lt'
      rw [eq'] at min_sub_b_rw
      have b0 : R.zero = b := by
        have mid_step : R.add min (R.neg min) = R.add (R.add min (R.neg b)) (R.neg min) := by
          rw (config := {occs := .pos [1]}) [min_sub_b_rw]
        rw [R.add_inv] at mid_step
        rw [R.add_comm] at mid_step
        rw [←R.add_assoc (R.neg min) min (R.neg b)] at mid_step
        rw [R.add_comm (R.neg min) min] at mid_step
        rw [R.add_inv] at mid_step
        rw [R.add_comm, R.add_zero] at mid_step
        have mid_step2 : R.neg (R.zero) = R.neg (R.neg b) := by
          rw [mid_step]
        rw [inv_of_inv] at mid_step2
        rw [inv_zero_eq_zero] at mid_step2
        exact mid_step2
      have zero_pos : R.zero ∈ R.P := by
        rw [b0]
        exact hb
      have zero_npos := R.trichotomy1
      contradiction

    have min_gt_min_sub_b : R.gt min_sub_b min := by
      unfold myOrderedRing.gt
      rw [min_sub_b_rw]
      rw [inv_eq_mul_neg1]
      rw [R.distrib]
      rw [←inv_eq_mul_neg1]
      rw [←R.add_assoc]
      rw [R.add_inv]
      rw [←inv_eq_mul_neg1]
      rw [inv_of_inv]
      rw [R.add_comm]
      rw [R.add_zero]
      exact hb

    have min_ngt_min_sub_b := lt_gt_contra R.tomyOrderedRing min_sub_b min min_lt_min_sub_b
    contradiction

theorem division_algorithm_uniqueness {α : Type} (R : WellOrderedRing α) (a b q r q' r' : α)
  (h : is_valid_division_result R a b q r)
  (h' : is_valid_division_result R a b q' r') :
  q = q' ∧ r = r' := by
  -- Unpack the hypotheses
  rcases h with ⟨ha, hb, heq, hge, hlt⟩
  rcases h' with ⟨ha', hb', heq', hge', hlt'⟩

  -- Subtract the two equations
  have h_diff : R.add (R.mul b (R.add q (R.neg q'))) (R.add r (R.neg r')) = R.zero := by
    rw [R.distrib]
    rw [←R.add_assoc]
    rw [R.add_assoc (R.mul b q) (R.mul b (R.neg q')) r]
    rw [R.add_comm (R.mul b (R.neg q')) r]
    rw [←R.add_assoc]
    rw [heq]
    rw [R.add_assoc]
    rw [R.mul_comm]
    rw [inv_eq_mul_neg1]
    rw [R.mul_assoc]
    rw [inv_eq_mul_neg1 R.tomyRing r']
    rw [←R.distrib]
    rw [R.mul_comm q' b]
    rw [heq']
    rw [←inv_eq_mul_neg1]
    rw [R.add_inv]

  have h_eq : R.mul b (R.add q (R.neg q')) = R.add r' (R.neg r) := by
    apply add_inv_to_zero R.tomyRing (R.mul b (R.add q (R.neg q'))) (R.add r' (R.neg r))
    rw [inv_add_distrib]
    rw [inv_of_inv]
    rw [R.add_comm (R.neg r') r]
    exact h_diff

  have b_div_r_diff : divisible R b (R.add r' (R.neg r)) := by
    unfold divisible
    use (R.add q (R.neg q'))

  have r_eq : r = r' := by
    have r_dichot := le_or_ge R.tomyOrderedRing r r'
    rcases r_dichot with (h_le | h_ge)
    sorry
    sorry

  sorry
