import UFT.Axioms
import UFT.RingResults
import UFT.OrderedRingResults
import UFT.IntegralDomain
import UFT.Division
import UFT.GCD
import UFT.EuclidsLemma

def power {α : Type} (R : WellOrderedRing α) (base : α) : α → α
  | exp =>
    if exp = R.zero then R.one  -- Base case: exponent is zero
    else R.mul base (power R base (R.sub exp R.one))  -- Recursive case
