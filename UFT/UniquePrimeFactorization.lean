import UFT.Axioms
import UFT.RingResults
import UFT.OrderedRingResults
import UFT.IntegralDomain
import UFT.Division
import UFT.GCD
import UFT.EuclidsLemma
import UFT.PrimeFactorizationExists

-- If a prime divides another prime, they are equal.
lemma prime_div_prime_implies_equality {α : Type} (R : WellOrderedRing α) (p : α) (q : α)
    (hp : prime R p) (hq : prime R q) (hdiv : divisible R p q) : p = q := by
  unfold prime at *
  rcases hp with ⟨pgt1, pprime⟩
  rcases hq with ⟨qgt1, qprime⟩
  unfold divisible at hdiv
  rcases hdiv with ⟨r, req⟩
  have p_gt0 := gt_transitive R.tomyOrderedRing p R.one R.zero pgt1 (one_gt_zero R.tomyOrderedRing)
  have p_pos := gt0_implies_pos R.tomyOrderedRing p p_gt0
  have q_pos := gt0_implies_pos R.tomyOrderedRing q (gt_transitive R.tomyOrderedRing q R.one R.zero qgt1 (one_gt_zero R.tomyOrderedRing))
  have r_pos := pos_a_mul_b_eq_pos_c R.tomyOrderedRing p r q p_pos  q_pos req
  have r_gt0 := pos_implies_gt0 R.tomyOrderedRing r r_pos
  have p1_or_r1 := qprime p r req p_gt0 r_gt0
  rcases p1_or_r1 with (p1 | r1)
  · rw [p1] at pgt1
    unfold myOrderedRing.gt at pgt1
    rw [R.add_inv] at pgt1
    have zero_npos := R.trichotomy1
    contradiction
  · rw [r1] at req
    rw [R.mul_ident] at req
    exact req

-- Pull a left factor out of a foldl product accumulator.
lemma foldl_mul_pull_left {α : Type} (R : WellOrderedRing α) (x t : α) :
    ∀ ys : List α, List.foldl R.mul (R.mul x t) ys = R.mul x (List.foldl R.mul t ys)
  | [] => by simp [List.foldl]
  | z :: zs => by
      -- (x * t) * z = x * (t * z) by associativity; then apply IH
      rw [List.foldl]
      rw [R.mul_assoc]
      simp [foldl_mul_pull_left R x (R.mul t z) zs]

-- Product of a list is head multiplied by product of tail.
lemma list_product_cons_eq_mul {α : Type} (R : WellOrderedRing α) (x : α) (xs : List α) :
    list_product R (x :: xs) = R.mul x (list_product R xs) := by
  unfold list_product
  change List.foldl R.mul (R.mul R.one x) xs = R.mul x (List.foldl R.mul R.one xs)
  have hxone : R.mul R.one x = R.mul x R.one := by
    rw [R.mul_comm]
  -- use the general pull-left lemma with t = 1
  simpa [hxone, R.mul_ident] using (foldl_mul_pull_left R x R.one xs)

-- Product over an appended list splits into product over each side.
lemma list_product_append {α : Type} (R : WellOrderedRing α) (l1 l2 : List α) :
    list_product R (l1 ++ l2) = R.mul (list_product R l1) (list_product R l2) := by
  unfold list_product
  simp [List.foldl_append]
  -- pull the left factor (foldl mul one l1) out of the second foldl
  simpa [R.mul_ident] using
    (foldl_mul_pull_left R (List.foldl R.mul R.one l1) R.one l2)

-- A prime is nonzero.
lemma prime_ne_zero {α : Type} (R : WellOrderedRing α) (p : α) (hp : prime R p) :
    p ≠ R.zero := by
  rcases hp with ⟨pgt1, _⟩
  have p_gt0 := gt_transitive R.tomyOrderedRing p R.one R.zero pgt1 (one_gt_zero R.tomyOrderedRing)
  have hne : R.zero ≠ p := gt_implies_neq R.tomyOrderedRing R.zero p p_gt0
  exact ne_comm.mp hne

-- Product of primes is positive.
lemma list_product_pos {α : Type} (R : WellOrderedRing α) :
    ∀ l : List α, (∀ q ∈ l, prime R q) → list_product R l ∈ R.P
  | [], _ => by
      unfold list_product
      simp [one_positive R.tomyOrderedRing]
  | q :: qs, hprimes => by
      have hq : prime R q := hprimes q (by simp)
      have hq_pos : q ∈ R.P := primes_pos R q hq
      have hqs_primes : ∀ q' ∈ qs, prime R q' := by
        intro q' hmem
        exact hprimes q' (by simp [hmem])
      have hqs_pos : list_product R qs ∈ R.P := list_product_pos R qs hqs_primes
      have : R.mul q (list_product R qs) ∈ R.P := R.P_mul q (list_product R qs) hq_pos hqs_pos
      simpa [list_product_cons_eq_mul R q qs] using this

-- If a prime divides a product of primes, it is one of the factors.
lemma extended_euclids_lemma {α : Type} (R : WellOrderedRing α) (p : α) (factor : List α)
    (hp : prime R p) (hfactor : ∀ q ∈ factor, prime R q)
    (hdiv : divisible R p (list_product R factor)) : p ∈ factor := by
  induction factor with
  | nil =>
      unfold list_product at hdiv
      unfold divisible at hdiv
      rcases hp with ⟨pgt1, _⟩
      rcases hdiv with ⟨k, pk_eq_one⟩
      have p_ne_zero : p ≠ R.zero := by
        have p_gt0 := gt_transitive R.tomyOrderedRing p R.one R.zero pgt1 (one_gt_zero R.tomyOrderedRing)
        exact lt_implies_neq R.tomyOrderedRing p R.zero (gt_rev_lt R.tomyOrderedRing R.zero p p_gt0)
      have one_ge_p : R.le R.one p := by
        have one_gt0 := one_gt_zero R.tomyOrderedRing
        exact a_div_b_then_a_leq_b R p R.one p_ne_zero one_gt0 (by
          unfold divisible
          use k
          exact pk_eq_one)
      have p_gt_one_as_lt : R.lt p R.one := gt_rev_lt R.tomyOrderedRing R.one p pgt1
      have not_lt := le_not_ltrev R.tomyOrderedRing R.one p one_ge_p
      exact (not_lt p_gt_one_as_lt).elim
  | cons q qs ih =>
      have hq : prime R q := hfactor q (by simp)
      have hq_pos : q ∈ R.P := primes_pos R q hq
      have hqs_primes : ∀ q' ∈ qs, prime R q' := by
        intro q' hmem
        exact hfactor q' (by simp [hmem])
      have hqs_pos : list_product R qs ∈ R.P := list_product_pos R qs hqs_primes
      have hdiv' : divisible R p (R.mul q (list_product R qs)) := by
        simpa [list_product_cons_eq_mul R q qs] using hdiv
      have hcases := euclids_lemma R q (list_product R qs) p hq_pos hqs_pos hp hdiv'
      rcases hcases with hdiv_p_q | hdiv_p_tail
      · have pq_eq : p = q := prime_div_prime_implies_equality R p q hp hq hdiv_p_q
        simp [pq_eq]
      · have ih_res := ih hqs_primes hdiv_p_tail
        simp [ih_res]

-- Split a list at a member into a prefix and suffix around that element.
lemma mem_split {α : Type} {a : α} {l : List α} (h : a ∈ l) :
    ∃ l1 l2, l = l1 ++ a :: l2 := by
  induction h with
  | head =>
      exact ⟨[], _, rfl⟩
  | tail b h ih =>
      rcases ih with ⟨l1, l2, rfl⟩
      exact ⟨b :: l1, l2, rfl⟩

-- A prime cannot divide 1.
lemma prime_not_div_one {α : Type} (R : WellOrderedRing α) (p : α) (hp : prime R p) :
    ¬ divisible R p R.one := by
  intro hdiv
  have p_ne_zero : p ≠ R.zero := prime_ne_zero R p hp
  rcases hp with ⟨pgt1, _⟩
  have one_gt0 := one_gt_zero R.tomyOrderedRing
  have one_le_p : R.le R.one p :=
    a_div_b_then_a_leq_b R p R.one p_ne_zero one_gt0 hdiv
  have p_gt0 := gt_transitive R.tomyOrderedRing p R.one R.zero pgt1 one_gt0
  have p_le_one : R.le p R.one :=
    a_div_b_then_a_leq_b R R.one p (one_not_zero R.tomyOrderedRing) p_gt0 (one_div_all R p)
  have p_eq_one := le_lerev_implies_eq R.tomyOrderedRing p R.one p_le_one one_le_p
  have p_ne_one : p ≠ R.one :=
    lt_implies_neq R.tomyOrderedRing p R.one (gt_rev_lt R.tomyOrderedRing R.one p pgt1)
  exact p_ne_one p_eq_one

-- If a product of primes is 1, the list must be empty.
lemma list_product_eq_one_implies_nil {α : Type} (R : WellOrderedRing α) :
    ∀ l : List α, (∀ q ∈ l, prime R q) → list_product R l = R.one → l = []
  | [], _, _ => rfl
  | p :: ps, hprimes, hprod => by
      have hp : prime R p := hprimes p (by simp)
      have hdiv : divisible R p R.one := by
        unfold divisible
        use list_product R ps
        calc
          R.mul p (list_product R ps) = list_product R (p :: ps) := by
            symm
            exact list_product_cons_eq_mul R p ps
          _ = R.one := hprod
      have hcontra := prime_not_div_one R p hp hdiv
      contradiction

-- Prime factorization is unique up to permutation.
theorem unique_prime_factorization {α : Type} (R : WellOrderedRing α) (n : α)
    (f1 f2 : List α) (hf1 : is_prime_factorization R n f1)
    (hf2 : is_prime_factorization R n f2) : List.Perm f1 f2 := by
  induction f1 generalizing n f2 with
  | nil =>
      rcases hf1 with ⟨hprimes1, hprod1⟩
      rcases hf2 with ⟨hprimes2, hprod2⟩
      have h1 : n = R.one := by
        calc
          n = list_product R [] := by symm; exact hprod1
          _ = R.one := by simp [list_product]
      have hprod2' : list_product R f2 = R.one := by
        simpa [h1] using hprod2
      have f2_nil : f2 = [] := list_product_eq_one_implies_nil R f2 hprimes2 hprod2'
      simpa [f2_nil] using (List.Perm.refl ([] : List α))
  | cons p ps ih =>
      rcases hf1 with ⟨hprimes1, hprod1⟩
      rcases hf2 with ⟨hprimes2, hprod2⟩
      have hp : prime R p := hprimes1 p (by simp)
      have hps_primes : ∀ q ∈ ps, prime R q := by
        intro q hq
        exact hprimes1 q (by simp [hq])
      have hdiv : divisible R p (list_product R f2) := by
        unfold divisible
        use list_product R ps
        calc
          R.mul p (list_product R ps) = list_product R (p :: ps) := by
            symm
            exact list_product_cons_eq_mul R p ps
          _ = n := hprod1
          _ = list_product R f2 := by symm; exact hprod2
      have hp_mem_f2 : p ∈ f2 := extended_euclids_lemma R p f2 hp hprimes2 hdiv
      rcases mem_split hp_mem_f2 with ⟨l1, l2, rfl⟩
      have hprimes_l1l2 : ∀ q ∈ l1 ++ l2, prime R q := by
        intro q hq
        apply hprimes2 q
        have hq' : q ∈ l1 ∨ q ∈ l2 := by
          simpa using (List.mem_append.mp hq)
        cases hq' with
        | inl hq1 =>
            exact List.mem_append_of_mem_left _ hq1
        | inr hq2 =>
            exact List.mem_append_of_mem_right _ (by simp [hq2])
      have hmid : list_product R (l1 ++ p :: l2) = R.mul p (list_product R (l1 ++ l2)) := by
        calc
          list_product R (l1 ++ p :: l2)
              = R.mul (list_product R l1) (list_product R (p :: l2)) := by
                  simpa [list_product_append R l1 (p :: l2)]
          _ = R.mul (list_product R l1) (R.mul p (list_product R l2)) := by
                  simp [list_product_cons_eq_mul R p l2]
          _ = R.mul p (R.mul (list_product R l1) (list_product R l2)) := by
                  rw [←R.mul_assoc, R.mul_comm (list_product R l1) p, R.mul_assoc]
          _ = R.mul p (list_product R (l1 ++ l2)) := by
                  simp [list_product_append R l1 l2]
      have hprod1' : R.mul p (list_product R ps) = n := by
        calc
          R.mul p (list_product R ps) = list_product R (p :: ps) := by
            symm
            exact list_product_cons_eq_mul R p ps
          _ = n := hprod1
      have hprod2' : R.mul p (list_product R (l1 ++ l2)) = n := by
        calc
          R.mul p (list_product R (l1 ++ l2)) = list_product R (l1 ++ p :: l2) := by
            symm
            exact hmid
          _ = n := hprod2
      have hmul_eq : R.mul p (list_product R ps) = R.mul p (list_product R (l1 ++ l2)) := by
        calc
          R.mul p (list_product R ps) = n := hprod1'
          _ = R.mul p (list_product R (l1 ++ l2)) := by symm; exact hprod2'
      have hcancel : list_product R ps = list_product R (l1 ++ l2) := by
        apply ordered_ring_cancellation R.tomyOrderedRing p (list_product R ps)
            (list_product R (l1 ++ l2)) (prime_ne_zero R p hp) hmul_eq
      have hpf_ps : is_prime_factorization R (list_product R ps) ps :=
        ⟨hps_primes, rfl⟩
      have hpf_l1l2 : is_prime_factorization R (list_product R ps) (l1 ++ l2) := by
        refine ⟨hprimes_l1l2, ?_⟩
        exact hcancel.symm
      have ih_perm : List.Perm ps (l1 ++ l2) :=
        ih (n := list_product R ps) (f2 := l1 ++ l2) hpf_ps hpf_l1l2
      have perm_cons : List.Perm (p :: ps) (p :: (l1 ++ l2)) := List.Perm.cons p ih_perm
      have perm_middle' : List.Perm (p :: (l1 ++ l2)) (l1 ++ p :: l2) := by
        have hmidperm : List.Perm (l1 ++ p :: l2) (p :: l1 ++ l2) := List.perm_middle
        simpa using hmidperm.symm
      exact perm_cons.trans perm_middle'
