import UFT.Axioms
import UFT.RingResults
import UFT.OrderedRingResults
import UFT.IntegralDomain
import UFT.Division
import UFT.GCD
import UFT.EuclidsLemma

def list_product {α : Type} (R : WellOrderedRing α) (l : List α) : α :=
  List.foldl R.mul R.one l

def is_prime_factorization {α : Type} (R : WellOrderedRing α) (n : α) (factors : List α) : Prop :=
    (∀ p ∈ factors, prime R p) ∧
    (list_product R factors = n)

def unique_prime_factorization {α : Type} (R : WellOrderedRing α) (n : α) : Prop :=
  ∀ (factors1 factors2 : List α),
    is_prime_factorization R n factors1 →
    is_prime_factorization R n factors2 →
    ∃ (perm : List α → List α),
      perm factors1 = factors2

lemma prime_have_prime_factorization {α : Type} (R : WellOrderedRing α) (p : α) (pprime : prime R p) : is_prime_factorization R p [p] := by
  unfold is_prime_factorization
  constructor
  · intro q hq
    simp at hq
    rw [hq]
    exact pprime
  · unfold list_product
    simp
    rw [R.mul_comm]
    rw [R.mul_ident]

theorem prime_factorization_exists {α : Type} (R : WellOrderedRing α) (n : α) (npos : R.gt R.one n) : ∃ (factors : List α), is_prime_factorization R n factors := by
  let S := {k : α | R.gt R.one k ∧ ¬∃ (pfactor : List α), is_prime_factorization R k pfactor}
  by_cases h : S.Nonempty
  · rcases h with ⟨eg, heg⟩
    rcases heg with ⟨eg_gt0, eg_nfactor⟩
    have rh : S.Nonempty := ⟨eg, ⟨eg_gt0, eg_nfactor⟩⟩
    have S_pos : S ⊆ R.P := by
      intro s hs
      rcases hs with ⟨sgt1, s_npfactor⟩
      have sgt0 := gt_transitive R.tomyOrderedRing s R.one R.zero sgt1 (one_gt_zero R.tomyOrderedRing)
      have spos := gt0_implies_pos R.tomyOrderedRing s sgt0
      exact spos
    have exist_least := R.well_ordered S rh S_pos
    rcases exist_least with ⟨l, hl, hl_least⟩
    rcases hl with ⟨lgt1, l_npfactor⟩
    have l_neq0 : l ≠ R.zero := by
      have l_gt0 := gt_transitive R.tomyOrderedRing l R.one R.zero lgt1 (one_gt_zero R.tomyOrderedRing)
      apply lt_implies_neq R.tomyOrderedRing l R.zero (gt_rev_lt R.tomyOrderedRing R.zero l l_gt0)
    have l_gt0 := gt_transitive R.tomyOrderedRing l R.one R.zero lgt1 (one_gt_zero R.tomyOrderedRing)
    have l_nprime : ¬prime R l := by
      intro l_prime
      have l_pfactor := prime_have_prime_factorization R l l_prime
      exact l_npfactor ⟨[l], l_pfactor⟩
    have l_composite := not_prime_implies_composite R l lgt1 l_nprime
    have l_have_prime_div := have_prime_divisor R l lgt1
    rcases l_have_prime_div with ⟨p, hp, hp_divisor⟩
    unfold divisible at hp_divisor
    rcases hp_divisor with ⟨q, qeq⟩
    have p_pos := primes_pos R p hp
    have p_neq1 : p ≠ R.one := by
      unfold prime at hp
      rcases hp with ⟨pgt1, pprime⟩
      exact lt_implies_neq R.tomyOrderedRing p R.one (gt_rev_lt R.tomyOrderedRing R.one p pgt1)
    have p_neql : p ≠ l := by
      intro pl
      rw [←pl] at l_nprime
      contradiction
    have q_neq1 : q ≠ R.one := by
      intro q1
      rw [q1] at qeq
      rw [R.mul_ident] at qeq
      contradiction
    have q_neql : q ≠ l := by
      intro ql
      rw [ql] at qeq
      rw [R.mul_comm] at qeq
      have p1 := unchange_imply_eq1 R.tomyOrderedRing l p l_neq0 qeq
      contradiction
    have q_neq0 : q ≠ R.zero := by
      intro q0
      rw [q0] at qeq
      rw [mul_zero] at qeq
      rw [qeq] at l_neq0
      contradiction
    have q_div_l : divisible R q l := by
      use p
      rw [R.mul_comm]
      exact qeq
    have q_le_l := a_div_b_then_a_leq_b R q l q_neq0 l_gt0 q_div_l
    have q_lt_l : R.lt l q := by
      unfold myOrderedRing.le at q_le_l
      rcases q_le_l with (qltl | qeql)
      · exact qltl
      · rw [qeql] at q_neql
        contradiction
    have q_not_in_S : q ∉ S := by
      intro qS
      have l_le_q := hl_least q qS
      have q_eq_l := le_lerev_implies_eq R.tomyOrderedRing q l l_le_q q_le_l
      rw [q_eq_l] at q_neql
      contradiction
    have q_pfactor : ∃ pfactor, is_prime_factorization R q pfactor := by
      by_contra q_pfactor
      apply q_not_in_S
      constructor
      · have q_pos := pos_a_mul_b_eq_pos_c R.tomyOrderedRing p q l p_pos (gt0_implies_pos R.tomyOrderedRing l l_gt0) qeq
        apply gt0_neq1_implies_gt1 R q (pos_implies_gt0 R.tomyOrderedRing q q_pos) q_neq1
      · exact q_pfactor
    rcases q_pfactor with ⟨q_pfactor, q_pfactor_prime_factorization⟩
    let l_factors := q_pfactor ++ [p]
    have l_prime_factorization : is_prime_factorization R l l_factors := by
      constructor
      · intro x hx
        cases List.mem_append.mp hx with
        | inl hx_in_q =>
          have x_prime := q_pfactor_prime_factorization.1 x hx_in_q
          exact x_prime
        | inr hx_is_p =>
          simp at hx_is_p
          rw [hx_is_p]
          exact hp
      · unfold list_product
        rw [List.foldl_append]
        unfold is_prime_factorization at q_pfactor_prime_factorization
        rcases q_pfactor_prime_factorization with ⟨q_pfactor_all_prime,q_pfactor_prod_eq⟩
        unfold list_product at q_pfactor_prod_eq
        rw [q_pfactor_prod_eq]
        simp
        rw [R.mul_comm]
        exact qeq
    have l_has_factorization : ∃ factors, is_prime_factorization R l factors := ⟨l_factors, l_prime_factorization⟩
    contradiction

  · have h_n_not_in_S : n ∉ S := by
      intro hn
      apply h
      exact ⟨n, hn⟩
    have h_n_factor : ∃ (pfactor : List α), is_prime_factorization R n pfactor := by
      by_contra h_no_factor
      apply h_n_not_in_S
      exact ⟨npos, h_no_factor⟩
    rcases h_n_factor with ⟨factors, h_factors⟩
    exact ⟨factors, h_factors⟩
