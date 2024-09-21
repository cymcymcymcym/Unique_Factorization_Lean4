import UFT.Axioms
import UFT.RingResults
import UFT.OrderedRingResults
import UFT.IntegralDomain
import UFT.Division
import UFT.GCD
import UFT.EuclidsLemma
import UFT.PrimeFactorizationExists

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

--tbc
