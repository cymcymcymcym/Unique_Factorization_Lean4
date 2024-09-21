import UFT.Axioms
import UFT.RingResults

-- P7 : `1 ∈ P ∧ -1 ∉ P`
lemma neg_one_mul_neg_one {α : Type} (R : myRing α) : R.mul (R.neg R.one) (R.neg R.one) = R.one := by
  rw [inv_mul_inv R R.one R.one]
  rw [R.mul_ident]

--salvage p2 here: one is not zero in an ordered ring
lemma one_not_zero {α : Type} (R : myOrderedRing α) : R.one ≠ R.zero := by
  by_contra h
  have h1 : ∀ a : α, R.mul a R.zero = R.zero := by
    intro a
    rw [mul_zero R.tomyRing a]
  have h2 : ∀ a : α, R.mul a R.zero = a := by
    intro a
    rw [←h]
    rw [R.mul_ident]
  have h3 : ∀ a : α, a = R.zero := by
    intro a
    rw [←h2 a]
    rw [h1]
  have h4 : ∀ a : α, a ∉ R.P := by
    intro a
    rw [h3 a]
    exact R.trichotomy1
  have h5 := R.P_nonempty
  rcases h5 with ⟨ b , h6 ⟩
  have h7 : b ∉ R.P := by
    apply h4
  exact h7 h6
  -- apply h7 exact h6

lemma neg_one_not_zero {α : Type} (R : myOrderedRing α) : R.neg R.one ≠ R.zero := by
  by_contra h
  have h1 : R.mul (R.neg R.one) (R.neg R.one) = R.mul (R.neg R.one) (R.zero) := by
    rw [h]
  have h2 : R.one = R.zero := by
    rw [←neg_one_mul_neg_one]
    rw [←mul_zero R.tomyRing (R.neg R.one)]
    exact h1
  exact one_not_zero R h2


theorem neg_one_not_pos {α : Type} (R : myOrderedRing α) : R.neg R.one ∉ R.P := by
  by_contra h1
  have h2 : R.mul (R.neg R.one) (R.neg R.one) = R.one := by rw [neg_one_mul_neg_one R.tomyRing]
  have h3 : R.one ∈ R.P := by
    rw [←h2]
    apply R.P_mul
    exact h1
    exact h1
  have h4 : R.neg R.one ∉ R.P := by
    apply R.trichotomy2 (R.one) h3
  contradiction

theorem one_positive {α : Type} (R : myOrderedRing α) : R.one ∈ R.P := by
  rw [←(inv_of_inv R.tomyRing R.one)]
  apply R.trichotomy3
  exact neg_one_not_pos R
  exact neg_one_not_zero R

def is_lt {α : Type} (R : myOrderedRing α) (a b : α) : Prop :=
  R.lt a b

def is_eq {α : Type} (a b : α) : Prop :=
  a = b

lemma gt_implies_neq {α : Type} (R : myOrderedRing α) (a b : α) (h : R.gt a b) :  a ≠ b := by
  unfold myOrderedRing.gt at h
  by_contra h1
  have h2 : R.add b (R.neg a) = R.zero := by
    rw [h1]
    rw [R.add_inv]
  have h3 : R.zero ∈ R.P := by
    rw [←h2]
    exact h
  have h4 : R.zero ∉ R.P := by
    exact R.trichotomy1
  contradiction

lemma lt_implies_neq {α : Type} (R : myOrderedRing α) (a b : α) (h : R.lt a b) : a ≠ b := by
  unfold myOrderedRing.lt at h
  by_contra h1
  have h2 : R.add a (R.neg b) = R.zero := by
    rw [h1]
    rw [R.add_inv]
  have h3 : R.zero ∈ R.P := by
    rw [←h2]
    exact h
  have h4 : R.zero ∉ R.P := by
    exact R.trichotomy1
  contradiction

lemma lt_rev_gt {α : Type} (R : myOrderedRing α) (a b : α) (h : R.lt a b) : R.gt b a := by
  unfold myOrderedRing.lt at h
  unfold myOrderedRing.gt
  exact h

lemma gt_rev_lt {α : Type} (R : myOrderedRing α) (a b : α) (h : R.gt a b) : R.lt b a := by
  unfold myOrderedRing.gt at h
  unfold myOrderedRing.lt
  exact h

lemma lt_not_refl {α : Type} (R : myOrderedRing α) (a : α) : ¬R.lt a a := by
  intro h
  unfold myOrderedRing.lt at h
  rw [R.add_inv] at h
  apply R.trichotomy1 h

lemma gt_not_refl {α : Type} (R : myOrderedRing α) (a : α) : ¬R.gt a a := by
  intro h
  unfold myOrderedRing.gt at h
  rw [R.add_inv] at h
  apply R.trichotomy1 h

lemma lt_gt_contra {α : Type} (R : myOrderedRing α) (a b : α) (h : R.lt a b) : ¬R.gt a b := by
  unfold myOrderedRing.gt
  unfold myOrderedRing.lt at h
  by_contra h1
  have h2 : R.add (R.add a (R.neg b)) (R.add b (R.neg a)) ∈ R.P := by
    apply R.P_add
    exact h
    exact h1
  have h3 : R.add (R.add a (R.neg b)) (R.add b (R.neg a)) = R.zero := by
    rw [R.add_assoc]
    rw [←R.add_assoc (R.neg b) b (R.neg a)]
    rw [R.add_comm (R.neg b) b]
    rw [R.add_inv]
    rw [R.add_comm R.zero (R.neg a)]
    rw [R.add_zero]
    rw [R.add_inv]

  have zero_pos: R.zero ∈ R.P := by
    rw [h3] at h2
    exact h2

  apply R.trichotomy1 zero_pos

lemma lt_implies_le {α : Type} (R : myOrderedRing α) (a b : α) (h : R.lt a b) : R.le a b := by
  unfold myOrderedRing.lt at h
  unfold myOrderedRing.le
  left
  exact h

theorem le_transitive {α : Type} (R : myOrderedRing α) (a b c :α) (h : R.le a b) (h' : R.le b c) : R.le a c :=by
  unfold myOrderedRing.le
  have h : R.lt a b ∨ a = b := h
  have h' : R.lt b c ∨ b = c := h'
  · by_cases h0 : is_lt R a b
    · by_cases h0' : is_lt R b c
      left
      have h1 : R.add a (R.neg b) ∈ R.P := h0
      have h1' : R.add b (R.neg c) ∈ R.P :=h0'
      have h1'' : R.add (R.add a (R.neg b)) (R.add b (R.neg c)) ∈ R.P := by
        apply R.P_add
        exact h1
        exact h1'
      rw [←(R.add_zero a)]
      rw [←(R.add_inv b)]
      rw (config := {occs := .pos [3]}) [R.add_comm]
      rw [←R.add_assoc a (R.neg b) b]
      rw [R.add_assoc (R.add a (R.neg b)) b (R.neg c)]
      exact h1''

      left
      have h2 : R.add a (R.neg b) ∈ R.P := h0
      have h2' : R.add b (R.neg c) ∉ R.P := h0'
      rcases h' with tmp | tmp
      have tmp' : R.add b (R.neg c) ∈ R.P := tmp
      exfalso
      exact h2' tmp'
      --other rcases
      rw [←tmp]
      exact h2

    · by_cases h0' : is_lt R b c
      left
      have h3 : R.add a (R.neg b) ∉ R.P := h0
      have h3' : R.add b (R.neg c) ∈ R.P := h0'
      rcases h with tmp | tmp
      have tmp' : R.add a (R.neg b) ∈ R.P := tmp
      exfalso
      exact h3 tmp'
      --other rcases
      rw [tmp]
      exact h3'

      right
      have h4 : R.add a (R.neg b) ∉ R.P := h0
      have h4' : R.add b (R.neg c) ∉ R.P := h0'
      rcases h with tmp | tmp
      have tmp' : R.add a (R.neg b) ∈ R.P := tmp
      exfalso
      exact h4 tmp'
      --other rcases
      rcases h' with tmp'' | tmp''
      have tmp''' : R.add b (R.neg c) ∈ R.P := tmp''
      exfalso
      exact h4' tmp'''
      rw [tmp]
      exact tmp''

theorem lt_transitive {α : Type} (R : myOrderedRing α) (a b c : α) (h : R.lt a b) (h' : R.lt b c) : R.lt a c := by
  unfold myOrderedRing.lt at h h'
  have h1 : R.add a (R.neg b) ∈ R.P := h
  have h2 : R.add b (R.neg c) ∈ R.P := h'
  have h3 : R.add (R.add a (R.neg b)) (R.add b (R.neg c)) ∈ R.P := by
    apply R.P_add
    exact h1
    exact h2

  rw [R.add_assoc a (R.neg b) (R.add b (R.neg c))] at h3
  rw [←R.add_assoc (R.neg b) b (R.neg c)] at h3
  rw [R.add_comm (R.neg b) b] at h3
  rw [R.add_inv] at h3
  rw [R.add_comm R.zero (R.neg c)] at h3
  rw [R.add_zero] at h3
  unfold myOrderedRing.lt
  exact h3

theorem gt_transitive {α : Type} (R : myOrderedRing α) (a b c : α) (h : R.gt b a) (h' : R.gt c b) : R.gt c a := by
  unfold myOrderedRing.gt at h h' ⊢
  have h1 : R.add a (R.neg b) ∈ R.P := h
  have h2 : R.add b (R.neg c) ∈ R.P := h'
  have h3 : R.add (R.add a (R.neg b)) (R.add b (R.neg c)) ∈ R.P := by
    apply R.P_add
    exact h1
    exact h2

  rw [R.add_assoc a (R.neg b) (R.add b (R.neg c))] at h3
  rw [←R.add_assoc (R.neg b) b (R.neg c)] at h3
  rw [R.add_comm (R.neg b) b] at h3
  rw [R.add_inv] at h3
  rw [R.add_comm R.zero (R.neg c)] at h3
  rw [R.add_zero] at h3
  exact h3

def is_gt {α : Type} (R : myOrderedRing α) (a b : α) : Prop :=
  R.gt a b

lemma inv_distrib_add {α : Type} (R : myRing α) (a b : α) : R.neg (R.add a b) = R.add (R.neg a) (R.neg b):= by
  rw [inv_eq_mul_neg1]
  rw [R.distrib]
  rw [←inv_eq_mul_neg1]
  rw [←inv_eq_mul_neg1]

lemma inv_zero_eq_zero {α : Type} (R : myRing α) : R.neg R.zero = R.zero := by
  have h0 : R.add R.zero (R.neg R.zero) = R.zero := by
    rw [R.add_inv]
  have h1 : R.add R.zero R.zero = R.zero := by
    rw [R.add_zero]
  apply inverse_unique R R.zero (R.neg R.zero) R.zero h0 h1

theorem one_gt_zero {α : Type} (R : myOrderedRing α) : R.gt R.zero R.one := by
  unfold myOrderedRing.gt
  rw [inv_zero_eq_zero]
  rw [R.add_zero]
  exact one_positive R

lemma gt0_implies_pos {α : Type} (R : myOrderedRing α) (a : α) (h : R.gt R.zero a) : a ∈ R.P := by
  unfold myOrderedRing.gt at h
  rw [inv_zero_eq_zero R.tomyRing, R.add_zero] at h
  exact h

lemma pos_implies_gt0 {α : Type} (R : myOrderedRing α) (a : α) (h : a ∈ R.P) : R.gt R.zero a := by
  unfold myOrderedRing.gt
  rw [inv_zero_eq_zero]
  rw [R.add_zero]
  exact h

theorem lt_eq_gt {α : Type} (R : myOrderedRing α) (a b : α) : ((R.lt a b) ∧ ¬(a = b) ∧ ¬(R.gt a b)) ∨
                                                            (¬(R.lt a b) ∧ (a = b) ∧ ¬(R.gt a b)) ∨
                                                            (¬(R.lt a b) ∧ ¬(a = b) ∧ (R.gt a b)) := by
  unfold myOrderedRing.lt
  unfold myOrderedRing.gt
  by_cases h0 : is_lt R a b
  · left
    have h0_0 : R.add a (R.neg b) ∈ R.P := by
      exact h0

    apply And.intro
    exact h0_0

    apply And.intro
    intro h0_1
    have h0_1' : R.add a (R.neg b) = R.zero := by
      rw [h0_1]
      rw [R.add_inv]
    have h0_1'' : R.add a (R.neg b) ∉ R.P := by
      rw [h0_1']
      exact R.trichotomy1
    exact h0_1'' h0_0

    have h0_2 : R.neg (R.add b (R.neg a) ) = R.add (R.neg b) a := by
      rw [inv_distrib_add]
      rw [inv_of_inv]
    have h0_2' : R.neg (R.add b (R.neg a) ) ∈ R.P := by
      rw [h0_2]
      rw [R.add_comm]
      exact h0_0
    have h0_2''p : R.neg (R.neg (R.add b (R.neg a) )) = R.add b (R.neg a) := by
      rw [inv_of_inv]
    have h0_2'' : R.add b (R.neg a) ∉ R.P := by
      rw [←h0_2''p]
      apply R.trichotomy2 (R.neg (R.add b (R.neg a) )) h0_2'
    exact h0_2''
  · right
    have h1_0 : R.add a (R.neg b) ∉ R.P := by
      exact h0
    by_cases g0 : is_eq a b
    · left
      have g0_0 : a = b := by
        exact g0

      apply And.intro
      exact h1_0

      apply And.intro
      exact g0_0

      have g0_2 : R.add b (R.neg a) ∉ R.P := by
        rw [g0]
        rw [R.add_inv]
        exact R.trichotomy1
      exact g0_2
    · right
      apply And.intro
      exact h1_0

      apply And.intro
      exact g0

      have g1_2 : R.neg (R.add b (R.neg a)) ∉ R.P := by
        rw [inv_distrib_add]
        rw [inv_of_inv]
        rw [R.add_comm]
        exact h1_0
      have g1_2' : R.add b (R.neg a) = R.neg (R.neg (R.add b (R.neg a))) := by
        rw [inv_of_inv]
      have g1_2'' : R.neg (R.add b (R.neg a)) ≠ R.zero := by
        rw [inv_distrib_add R.tomyRing b (R.neg a)]
        rw [inv_of_inv]
        rw [R.add_comm]
        intro h
        have g1_2''' : a = b := by
          apply add_inv_to_zero R.tomyRing a b h
        exact g0 g1_2'''
      have g1_2''' : R.add b (R.neg a) ∈ R.P := by
        rw [g1_2']
        apply R.trichotomy3 (R.neg (R.add b (R.neg a))) g1_2 g1_2''
      exact g1_2'''

theorem le_or_ge {α : Type} (R : myOrderedRing α) (a b : α) : R.le a b ∨ R.ge a b := by
  have ab_trich := lt_eq_gt R a b
  rcases ab_trich with (b_lt_a | b_eq_a | b_gt_a)
  · rcases b_lt_a with ⟨in_use, tmp1, tmp2⟩
    left
    unfold myOrderedRing.lt at in_use
    unfold myOrderedRing.le
    left
    exact in_use
  · rcases b_eq_a with ⟨tmp1, in_use, tmp2⟩
    left
    unfold myOrderedRing.le
    right
    exact in_use
  · rcases b_gt_a with ⟨tmp1, tmp2, in_use⟩
    right
    unfold myOrderedRing.gt at in_use
    unfold myOrderedRing.ge
    left
    exact in_use

theorem le_not_ltrev {α : Type} (R : myOrderedRing α) (a b : α) (h : R.le a b) : ¬R.lt b a := by
  unfold myOrderedRing.lt
  unfold myOrderedRing.le at h
  rcases h with (hlt | heq)
  · have hltrev := R.trichotomy2 (R.add a (R.neg b)) hlt
    rw [inv_add_distrib] at hltrev
    rw [inv_of_inv] at hltrev
    rw [R.add_comm] at hltrev
    exact hltrev
  · rw [heq]
    rw [R.add_inv]
    exact R.trichotomy1

theorem le_lerev_implies_eq {α : Type} (R : myOrderedRing α) (a b : α) (h : R.le a b) (h' : R.le b a) : a = b := by
  unfold myOrderedRing.le at h
  unfold myOrderedRing.le at h'
  rcases h with (b_lt_a | b_eq_a)
  · rcases h' with (a_lt_b | a_eq_b)
    · have b_lt_a' : R.lt a b := b_lt_a
      have b_gt_a : R.gt a b := a_lt_b
      have nb_gt_a : ¬(R.gt a b) := lt_gt_contra R a b b_lt_a
      contradiction
    · rw [a_eq_b]
  · exact b_eq_a

theorem nonzero_sq_pos {α : Type} (R : myOrderedRing α) (a : α) (h : a ≠ R.zero) : (R.mul a a) ∈ R.P := by
  have trich := lt_eq_gt R a R.zero
  rcases trich with (a_pos | a_zero | a_neg)
  · rcases a_pos with ⟨a_pos', tmp11, tmp12⟩
    unfold myOrderedRing.lt at a_pos'
    rw [inv_zero_eq_zero] at a_pos'
    rw [R.add_zero] at a_pos'
    apply R.P_mul a a a_pos' a_pos'
  · rcases a_zero with ⟨tmp21, a_zero', tmp22⟩
    contradiction
  · rcases a_neg with ⟨tmp31, tmp32,a_neg'⟩
    unfold myOrderedRing.gt at a_neg'
    rw [R.add_comm] at a_neg'
    rw [R.add_zero] at a_neg'
    rw [←inv_mul_inv]
    apply R.P_mul (R.neg a) (R.neg a) a_neg' a_neg'

lemma pos_a_mul_b_eq_pos_c {α : Type} (R : myOrderedRing α) (a b c : α) (ha : a ∈ R.P) (hc : c ∈ R.P) (heq : R.mul a b = c) : b ∈ R.P := by
  have trich_b := lt_eq_gt R b R.zero
  rcases trich_b with (b_gt_zero | b_eq_zero | b_lt_zero)
  · rcases b_gt_zero with ⟨in_use, tmp11, tmp12⟩
    unfold myOrderedRing.lt at in_use
    rw [inv_zero_eq_zero] at in_use
    rw [R.add_zero] at in_use
    exact in_use
  · rcases b_eq_zero with ⟨tmp21, in_use, tmp22⟩
    rw [in_use] at heq
    rw [mul_zero R.tomyRing a] at heq
    rw [←heq] at hc
    have zero_npos := R.trichotomy1
    contradiction
  · rcases b_lt_zero with ⟨tmp11, tmp12, in_use⟩
    unfold myOrderedRing.gt at in_use
    rw [R.add_comm] at in_use
    rw [R.add_zero] at in_use
    have neg_c_pos : R.neg c ∈ R.P := by
      rw [←heq]
      rw [R.mul_comm]
      rw [inv_assoc]
      exact R.P_mul (R.neg b) a in_use ha
    have neg_c_npos := R.trichotomy2 c hc
    contradiction

--P10 : ( b ≤ a , y ≤ x) → ( b + y ≤ a + x )
theorem lt_add {α : Type} (R : myOrderedRing α) (a b x y: α) (h : R.le a b) (h' : R.le x y ) :
  R.le (R.add a x) (R.add b y) := by
  unfold myOrderedRing.le
  · by_cases h0 : is_lt R a b
    · by_cases h0' : is_lt R x y
      left
      have h1 : R.add a (R.neg b) ∈ R.P := h0
      have h1' : R.add x (R.neg y) ∈ R.P := h0'
      rw [inv_eq_mul_neg1 R.tomyRing]
      rw [R.distrib]
      rw [←inv_eq_mul_neg1 R.tomyRing b]
      rw [←inv_eq_mul_neg1 R.tomyRing y]
      rw (config := {occs := .pos [2]}) [R.add_comm]
      rw [←R.add_assoc]
      rw [R.add_assoc x a (R.neg b)]
      rw (config := {occs := .pos [2]}) [R.add_comm]
      rw [R.add_assoc]
      apply R.P_add
      exact h1
      exact h1'

      left
      have h2 : R.add a (R.neg b) ∈ R.P := h0
      have h2' : R.add x (R.neg y) ∉ R.P := h0'
      rcases h' with tmp | tmp
      exfalso
      exact h2' tmp
      --other rcases
      have tmp' : R.add x (R.neg y) = R.zero := by
        rw [tmp]
        rw [R.add_inv]
      rw [inv_distrib_add]
      rw [R.add_comm (R.neg b) (R.neg y)]
      rw [R.add_assoc a x (R.add (R.neg y) (R.neg b))]
      rw [←R.add_assoc x (R.neg y) (R.neg b)]
      rw [R.add_comm (R.add x (R.neg y)) (R.neg b)]
      rw [←R.add_assoc]
      rw [tmp']
      rw [R.add_zero]
      exact h2

    · by_cases h0' : is_lt R x y
      left
      have h3 : R.add a (R.neg b) ∉ R.P := h0
      have h3' : R.add x (R.neg y) ∈ R.P := h0'
      rcases h with tmp | tmp
      exfalso
      exact h3 tmp
      --other rcases
      have tmp' : R.add a (R.neg b) = R.zero := by
        rw [tmp]
        rw [R.add_inv]
      rw [inv_distrib_add]
      rw [R.add_comm (R.neg b) (R.neg y)]
      rw [R.add_assoc a x (R.add (R.neg y) (R.neg b))]
      rw [←R.add_assoc x (R.neg y) (R.neg b)]
      rw [R.add_comm (R.add x (R.neg y)) (R.neg b)]
      rw [←R.add_assoc]
      rw [tmp']
      rw [R.add_comm]
      rw [R.add_zero]
      exact h3'

      right
      have h4 : R.add a (R.neg b) ∉ R.P := h0
      have h4' : R.add x (R.neg y) ∉ R.P := h0'
      rcases h with tmp | tmp
      exfalso
      exact h4 tmp
      have h4'' : x = y := by
        rcases h' with tmp' | tmp'
        exfalso
        exact h4' tmp'
        exact tmp'
      rw [tmp]
      rw [h4'']

theorem pos_mult_compatible_leq {α : Type} (R : myOrderedRing α) (a b x y : α) (ha : a ∈ R.P) (hb : b ∈ R.P) (hx : x ∈ R.P) (hy : y ∈ R.P)
  (h1 : R.le a b) (h2 : R.le x y) : R.le (R.mul a x) (R.mul b y) := by
  have h3 : R.le (R.mul a x) (R.mul a y) := by
    unfold myOrderedRing.le
    · by_cases ylex : is_lt R x y
      left
      have h3_0 : R.add x (R.neg y) ∈ R.P := ylex
      rw [R.mul_comm a y]
      rw [inv_assoc]
      rw [R.mul_comm (R.neg y) a]
      rw [←R.distrib]
      apply R.P_mul a (R.add x (R.neg y)) ha h3_0

      right
      have h3_1 : R.add x (R.neg y) ∉ R.P := ylex
      have h3_2 : x = y := by
        rcases h2 with tmp | tmp
        exfalso
        exact h3_1 tmp
        exact tmp
      rw [h3_2]

  have h4 : R.le (R.mul a y) (R.mul b y) := by
    unfold myOrderedRing.le
    · by_cases h4_0 : is_lt R a b
      left
      have h4_1 : R.add a (R.neg b) ∈ R.P := h4_0
      rw [inv_assoc]
      rw [R.mul_comm (R.neg b) y]
      rw [R.mul_comm a y]
      rw [←R.distrib]
      apply R.P_mul y (R.add a (R.neg b)) hy h4_1

      right
      have h4_2 : R.add a (R.neg b) ∉ R.P := h4_0
      have h4_3 : a = b := by
        rcases h1 with tmp | tmp
        exfalso
        exact h4_2 tmp
        exact tmp
      rw [h4_3]

  have h5 : R.le (R.mul a x) (R.mul b y) := by
    apply le_transitive R (R.mul a x) (R.mul a y) (R.mul b y) h3 h4

  exact h5
