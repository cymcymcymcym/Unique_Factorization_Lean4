import UFT.Axioms
import UFT.RingResults
import UFT.OrderedRingResults
import UFT.IntegralDomain
import UFT.Division

def is_gcd {α : Type} (R : WellOrderedRing α) (n a b : α) : Prop :=
  a ≠ R.zero ∧
  b ≠ R.zero ∧
  R.gt R.zero n ∧
  divisible R n a ∧
  divisible R n b ∧
  (∀ x : α, divisible R x a → divisible R x b → R.le n x)

lemma div_linear_comb {α : Type} (R : WellOrderedRing α) (a b : α) : ∀ n x y: α,
  divisible R n a → divisible R n b →
  divisible R n (R.add (R.mul a x) (R.mul b y)) := by
  intro n x y ndiv_a ndiv_b
  rcases ndiv_a with ⟨qa, qa_eq⟩
  rcases ndiv_b with ⟨qb, qb_eq⟩
  have linear_comb_rearrange : (R.add (R.mul a x) (R.mul b y)) = R.mul n (R.add (R.mul qa x) (R.mul qb y)) := by
    rw [←qa_eq, ←qb_eq]
    rw [R.mul_assoc, R.mul_assoc]
    rw [←R.distrib]
  rw [linear_comb_rearrange]
  unfold divisible
  use (R.add (R.mul qa x) (R.mul qb y))

theorem bezout {α : Type} (R : WellOrderedRing α) (a b : α) (ha : a ∈ R.P) (hb : b ∈ R.P):
  ∃ (x y d : α), is_gcd R d a b ∧ R.add (R.mul a x) (R.mul b y) = d := by
  let S := {s : α | ∃ x y : α, s = R.add (R.mul a x) (R.mul b y) ∧ R.gt R.zero s}

  have a_neq0 : a ≠ R.zero := by
    intro h
    rw [h] at ha
    have zero_npos := R.trichotomy1
    contradiction

  have b_neq0 : b ≠ R.zero := by
    intro h
    rw [h] at hb
    have zero_npos := R.trichotomy1
    contradiction

  have h_S_nonempty : S.Nonempty := by
    --prove R.add (R.mul a a) (R.mul b b) is in S
    use R.add (R.mul a a) (R.mul b b)
    use a, b
    constructor
    · rfl  -- This proves s = ax + by
    · unfold myOrderedRing.gt
      rw [inv_zero_eq_zero]
      rw [R.add_zero]
      apply R.P_add (R.mul a a) (R.mul b b)
      exact nonzero_sq_pos R.tomyOrderedRing a a_neq0
      exact nonzero_sq_pos R.tomyOrderedRing b b_neq0

  have h_S_pos : S ⊆ R.P := by
    intro s hs
    rcases hs with ⟨xtmp, ytmp, s_eq, s_gt0⟩
    unfold myOrderedRing.gt at s_gt0
    rw [inv_zero_eq_zero] at s_gt0
    rw [R.add_zero] at s_gt0
    exact s_gt0

  have h_min : ∃ d ∈ S, ∀ s ∈ S, R.le s d := by
    apply R.well_ordered S h_S_nonempty h_S_pos

  -- Extract the minimum element and its properties
  rcases h_min with ⟨d, ⟨x, y, hd_eq, hd_gt0⟩, hd_min⟩
  have d_pos : d ∈ R.P := by
    unfold myOrderedRing.gt at hd_gt0
    rw [inv_zero_eq_zero] at hd_gt0
    rw [R.add_zero] at hd_gt0
    exact hd_gt0

  -- d div a
  have div_exist_ad := division_algorithm_existence R a d ha d_pos
  rcases div_exist_ad with ⟨qa, ra, hda⟩
  rcases hda with ⟨a_pos, d_pos', div_eq, ra_ge0, ra_ltd⟩

  have ra_rearranged : ra = R.add a (R.neg (R.mul d qa)) := by
    rw [R.add_comm] at div_eq
    apply solve_for_add R.tomyRing ra (R.mul d qa) a div_eq

  let acoeff := (R.add R.one (R.neg (R.mul qa x)))
  let bcoeff := (R.neg (R.mul qa y))

  have ra_linear_comb : ra = R.add (R.mul a acoeff) (R.mul b bcoeff) := by
    rw [hd_eq] at ra_rearranged
    rw [R.mul_comm (R.add (R.mul a x) (R.mul b y)) qa] at ra_rearranged
    rw [R.distrib] at ra_rearranged
    rw [←R.mul_assoc qa a x] at ra_rearranged
    rw [R.mul_comm qa a] at ra_rearranged
    rw [R.mul_assoc a qa x] at ra_rearranged
    rw [inv_eq_mul_neg1 R.tomyRing (R.add (R.mul a (R.mul qa x)) (R.mul qa (R.mul b y)))] at ra_rearranged
    rw [R.distrib] at ra_rearranged
    rw [R.mul_comm a (R.mul qa x)] at ra_rearranged
    rw [←inv_eq_mul_neg1] at ra_rearranged
    rw [inv_assoc] at ra_rearranged
    rw [R.mul_comm (R.neg (R.mul qa x)) a] at ra_rearranged
    rw [←R.add_assoc] at ra_rearranged
    rw (config := {occs := .pos [1]}) [←R.mul_ident a] at ra_rearranged
    rw [←R.distrib] at ra_rearranged
    rw [←R.mul_assoc qa b y] at ra_rearranged
    rw [R.mul_comm qa b] at ra_rearranged
    rw [R.mul_assoc] at ra_rearranged
    rw [R.mul_comm b (R.mul qa y)] at ra_rearranged
    rw [←inv_eq_mul_neg1] at ra_rearranged
    rw (config := {occs := .pos [2]}) [inv_assoc] at ra_rearranged
    rw [R.mul_comm (R.neg (R.mul qa y)) b] at ra_rearranged
    exact ra_rearranged

  have ra0 : ra = R.zero := by
    unfold myOrderedRing.ge at ra_ge0
    rcases ra_ge0 with (ra_pos | ra_eq0)
    · have ra_in_S : ra ∈ S := by
        use acoeff
        use bcoeff
        constructor
        · exact ra_linear_comb
        · unfold myOrderedRing.gt
          exact ra_pos

      have d_le_ra := hd_min ra ra_in_S
      have d_neq_ra := gt_implies_neq R.tomyOrderedRing ra d ra_ltd
      have d_lt_ra : R.lt ra d := by
        unfold myOrderedRing.lt
        unfold myOrderedRing.le at d_le_ra
        rcases d_le_ra with (lt' | eq')
        · exact lt'
        · contradiction
      have d_ngt_ra := lt_gt_contra R.tomyOrderedRing ra d d_lt_ra
      contradiction
    · rw [ra_eq0]

  have d_div_a : divisible R d a := by
    use qa
    rw [ra0] at div_eq
    rw [R.add_zero] at div_eq
    exact div_eq


  -- d div b (WLOG)
  have div_exist_bd := division_algorithm_existence R b d hb d_pos
  rcases div_exist_bd with ⟨qb, rb, hdb⟩
  rcases hdb with ⟨b_pos, d_pos'', div_eq_b, rb_ge0, rb_ltd⟩

  have rb_rearranged : rb = R.add b (R.neg (R.mul d qb)) := by
    rw [R.add_comm] at div_eq_b
    apply solve_for_add R.tomyRing rb (R.mul d qb) b div_eq_b

  let bcoeff' := (R.add R.one (R.neg (R.mul qb y)))
  let acoeff' := (R.neg (R.mul qb x))

  have rb_linear_comb : rb = R.add (R.mul a acoeff') (R.mul b bcoeff') := by
    rw [hd_eq] at rb_rearranged
    rw [R.mul_comm (R.add (R.mul a x) (R.mul b y)) qb] at rb_rearranged
    rw [R.distrib] at rb_rearranged
    rw [←R.mul_assoc qb b y] at rb_rearranged
    rw [R.mul_comm qb b] at rb_rearranged
    rw [R.mul_assoc b qb y] at rb_rearranged
    rw [inv_eq_mul_neg1 R.tomyRing (R.add (R.mul qb (R.mul a x)) (R.mul b (R.mul qb y)))] at rb_rearranged
    rw [R.distrib] at rb_rearranged
    rw [R.mul_comm b (R.mul qb y)] at rb_rearranged
    rw (config := {occs := .pos [2]}) [←inv_eq_mul_neg1] at rb_rearranged
    rw [inv_assoc] at rb_rearranged
    rw [R.mul_comm (R.neg (R.mul qb y)) b] at rb_rearranged
    rw [R.add_comm] at rb_rearranged
    rw [R.add_assoc] at rb_rearranged
    rw (config := {occs := .pos [2]}) [←R.mul_ident b] at rb_rearranged
    rw [←R.distrib] at rb_rearranged
    rw [R.add_comm (R.neg (R.mul qb y)) R.one] at rb_rearranged
    rw [←R.mul_assoc qb a x] at rb_rearranged
    rw [R.mul_comm qb a] at rb_rearranged
    rw [R.mul_assoc a qb x] at rb_rearranged
    rw [R.mul_comm a (R.mul qb x)] at rb_rearranged
    rw [←inv_eq_mul_neg1] at rb_rearranged
    rw [inv_assoc] at rb_rearranged
    rw [R.mul_comm] at rb_rearranged
    exact rb_rearranged


  have rb0 : rb = R.zero := by
    unfold myOrderedRing.ge at rb_ge0
    rcases rb_ge0 with (rb_pos | rb_eq0)
    · have rb_in_S : rb ∈ S := by
        use acoeff'
        use bcoeff'
        constructor
        · exact rb_linear_comb
        · unfold myOrderedRing.gt
          exact rb_pos

      have d_le_rb := hd_min rb rb_in_S
      have d_neq_rb := gt_implies_neq R.tomyOrderedRing rb d rb_ltd
      have d_lt_rb : R.lt rb d := by
        unfold myOrderedRing.lt
        unfold myOrderedRing.le at d_le_rb
        rcases d_le_rb with (lt' | eq')
        · exact lt'
        · contradiction
      have d_ngt_rb := lt_gt_contra R.tomyOrderedRing rb d d_lt_rb
      contradiction
    · rw [rb_eq0]

  have d_div_b : divisible R d b := by
    use qb
    rw [rb0] at div_eq_b
    rw [R.add_zero] at div_eq_b
    exact div_eq_b


  have common_divisor_div_d : ∀ (e : α), divisible R e a ∧ divisible R e b → divisible R e d := by
    intro e e_div
    rcases e_div with ⟨e_div_a, e_div_b⟩
    have div_linear_comb_form_d :=div_linear_comb R a b e x y e_div_a e_div_b
    rw [hd_eq]
    exact div_linear_comb_form_d

  have common_divisor_le_d : ∀ (e : α), divisible R e a ∧ divisible R e b → R.le d e := by
    intro e e_div
    rcases e_div with ⟨e_div_a, e_div_b⟩
    have e_div_d := common_divisor_div_d e ⟨e_div_a,e_div_b⟩
    have e_neq0 : e ≠ R.zero := by
      intro e_eq0
      rcases e_div_a with ⟨eqa, eqa_eq⟩
      rw [R.mul_comm] at eqa_eq
      rw [e_eq0] at eqa_eq
      rw [mul_zero] at eqa_eq
      have zero_pos : R.zero ∈ R.P := by
        rw [eqa_eq]
        exact a_pos
      have zero_npos := R.trichotomy1
      contradiction
    apply a_div_b_then_a_leq_b R e d e_neq0 hd_gt0 e_div_d

  have common_divisor_le_d' : ∀ (x : α), divisible R x a → divisible R x b → R.le d x := by
    intro x x_div_a x_div_b
    have x_div : divisible R x a ∧ divisible R x b := ⟨x_div_a, x_div_b⟩
    exact common_divisor_le_d x x_div

  have d_gcd : is_gcd R d a b := by
    unfold is_gcd
    exact ⟨a_neq0, b_neq0, hd_gt0, d_div_a, d_div_b, common_divisor_le_d'⟩

  have hd_eq' : R.add (R.mul a x) (R.mul b y) = d := by
   rw [hd_eq]

  use x, y, d
