import UFT.Axioms

--P1 : zero is unique
theorem zero_unique {α : Type} (R : myRing α) (z z' : α)
  (hz : ∀ x : α, R.add x z = x) (hz' : ∀ x : α, R.add x z' = x) : z = z' :=
  have h1 : R.add z z' = z := by rw [hz']
  have h2 : R.add z' z = z' := by rw [hz]
  have h3 : R.add z z' = R.add z' z := by rw [R.add_comm]
  have h4 : z = z' := by rw [←h1, h3, h2]
  by exact h4

--P2 : 0 = 1 is False, salvage see theorem `one_not_zero` for `OrderedRing`

--P3 : ` a + b = a + b' → b = b' `
theorem right_add_eq {α : Type} (R : myRing α) (a b b' : α)
  (h : R.add a b = R.add a b') : b = b' := by
  have h0 : R.add (R.neg a) (R.add a b) = R.add (R.neg a) (R.add a b') := by
    rw [h]
  have h1 : b = R.add (R.neg a) (R.add a b) := by
    rw [←R.add_assoc (R.neg a) a b ]
    rw [R.add_comm (R.neg a) a]
    rw [R.add_inv]
    rw [R.add_comm (R.zero) b]
    rw [R.add_zero]
  have h2 : b' = R.add (R.neg a) (R.add a b') := by
    rw [←R.add_assoc (R.neg a) a b']
    rw [R.add_comm (R.neg a) a]
    rw [R.add_inv]
    rw [R.add_comm (R.zero) b']
    rw [R.add_zero]
  rw [h2]
  rw [h1]
  exact h0

theorem left_add_eq {α : Type} (R : myRing α) (a b b' : α)
  (h : R.add b a = R.add b' a) : b = b' := by
  have h1 : R.add b (R.add a (R.neg a)) = R.add b' (R.add a (R.neg a)) := by
    rw [←R.add_assoc b a (R.neg a)]
    rw [←R.add_assoc b' a (R.neg a)]
    rw [h]

  have h2 : R.add a (R.neg a) = R.zero := by
    rw [R.add_inv]
  rw [h2] at h1
  rw [R.add_zero, R.add_zero] at h1
  exact h1

theorem solve_for_add {α : Type} (R : myRing α) (a b c: α) (h : R.add a b = c) : a = R.add c (R.neg b) := by
  rw [←h]
  rw [R.add_assoc]
  rw [R.add_inv]
  rw [R.add_zero]

--P4 (1) : inverse is unique
theorem inverse_unique {α : Type} (R : myRing α) (a b b' : α)
  (h : R.add a b = R.zero) (h' : R.add a b' = R.zero) : b = b' :=
  have h0 : R.add a b = R.add a b' := by
    rw [h]
    rw [h']
  suffices h0': R.add a b = R.add a b' from (right_add_eq R a b b' h0')
  show R.add a b = R.add a b' from h0
  --`show b = b' from (right_add_eq R a b b' h0)`

--P4 (2) : `-(-a) = a`
theorem inv_of_inv {α : Type} (R : myRing α) (a : α) : R.neg (R.neg a) = a :=
  have h0 : R.add (R.neg a) (R.neg (R.neg a)) = R.zero := by
    rw [R.add_inv]
  have h1 : R.add (R.neg a) a = R.zero := by
    rw [R.add_comm]
    rw [R.add_inv]
  inverse_unique R (R.neg a) (R.neg (R.neg a)) a h0 h1

--P4 (3) : ` -(ab) = -a(b) `
lemma mul_zero {α : Type} (R: myRing α) (a : α) : R.mul a R.zero = R.zero := -- `a * 0 =a`
  have h0 : R.add R.zero R.zero = R.zero := by rw [R.add_zero] --0 + 0 = 0
  have h1 : R.add (R.mul a R.zero) (R.mul a R.zero ) = R.mul a R.zero:= by --a0 + a0 = a0
    rw (config := {occs := .pos [3]}) [←h0]
    rw [R.distrib]
  have h2 : R.add (R.mul a R.zero) R.zero = R.mul a R.zero := by rw [R.add_zero] --a0 + 0 = a0
  have h3 : R.add (R.mul a R.zero) (R.mul a R.zero) = R.add (R.mul a R.zero) R.zero := by -- a0 + a0 = a0 + 0
    rw [h1]
    rw [h2]
  show R.mul a R.zero = R.zero from (right_add_eq R (R.mul a R.zero) (R.mul a R.zero) R.zero h3)

theorem inv_assoc {α : Type} (R : myRing α) (a b : α) : R.neg (R.mul a b) = R.mul (R.neg a) b :=
  have h1 : R.add (R.mul a b) (R.neg (R.mul a b))= R.zero := by
    rw [R.add_inv]
  have h2' : R.add (R.mul a b) (R.mul (R.neg a) b) = R.mul (R.add (R.neg a) a) b := by
    rw [R.mul_comm (R.add (R.neg a) a) b]
    rw [R.distrib b (R.neg a) a]
    rw [R.mul_comm (R.neg a) b]
    rw [R.mul_comm a b]
    rw [R.add_comm (R.mul b (R.neg a)) (R.mul b a)]
  have h2 : R.add (R.mul a b) (R.mul (R.neg a) b) = R.zero := by
    rw [h2']
    rw [R.add_comm (R.neg a) a]
    rw [R.add_inv]
    rw [R.mul_comm R.zero b]
    rw [mul_zero R b]
  have h3 : R.add (R.mul a b) (R.mul (R.neg a) b) = R.add (R.mul a b) (R.neg (R.mul a b)) := by
    rw [h2]
    rw [h1]
  show R.neg (R.mul a b) = R.mul (R.neg a) b from (right_add_eq R (R.mul a b) (R.mul (R.neg a) b) (R.neg (R.mul a b)) h3).symm

--P4 (4) : ` (-a)(-b) = ab `
theorem inv_mul_inv {α : Type} (R : myRing α) (a b : α) : R.mul (R.neg a) (R.neg b) = R.mul a b := by
  rw [←inv_assoc R a (R.neg b)]
  rw [R.mul_comm]
  rw [inv_assoc]
  rw [inv_of_inv]
  rw [R.mul_comm]

--P4 (5) : ` -a = (-1) a `
theorem inv_eq_mul_neg1 {α : Type} (R : myRing α) (a : α) : R.neg a = R.mul (R.neg R.one) a := by
 rw [←inv_assoc]
 rw [R.mul_comm R.one a]
 rw [R.mul_ident]

theorem inv_add_distrib {α : Type} (R : myRing α) (a b : α) : R.neg (R.add a b) = R.add (R.neg a) (R.neg b) := by
  rw [inv_eq_mul_neg1]
  rw [R.distrib]
  rw [←inv_eq_mul_neg1, ←inv_eq_mul_neg1]

--P6 salvage : ( a ≠ 0, ab = ab' → b = b' ) ⇔ ( ab = 0 → a = 0 ∨ b = 0 )
lemma add_inv_to_zero {α : Type} (R : myRing α) (a b: α) (h : R.add a (R.neg b) = R.zero) :  a = b :=by
  have h0 : R.add (R.add a (R.neg b)) b = b := by
    rw (config := {occs := .pos [3]}) [←(R.add_zero b)]
    rw [R.add_comm b R.zero]
    rw [h]
  have h2 : a = b := by
    rw [←R.add_zero a]
    rw [←R.add_inv b]
    rw [R.add_comm b (R.neg b)]
    rw [←R.add_assoc]
    exact h0
  exact h2

lemma add_inv_to_zero_reverse {α : Type} (R : myRing α) (a b: α) (h : a = b) : R.add a (R.neg b) = R.zero := by
  rw [h]
  rw [R.add_inv]

def is_integral_domain {α : Type}(R : myRing α):=
  ∀ a b, (R.mul a b = R.zero → a = R.zero ∨ b = R.zero)

def is_zero {α : Type}(R : myRing α)(x : α):=
  x = R.zero

theorem mul_inv_zero_divisor {α : Type} (R : myRing α) :
  (∀ a b b': α, (a ≠ R.zero)→(R.mul a b = R.mul a b' → b = b')) ↔ is_integral_domain R:= by
  unfold is_integral_domain
  constructor
  · intro h
    intro x y
    intro h'
    have h'' : R.mul x y = R.mul x R.zero := by
      rw [mul_zero]
      exact h'
    --apply h h''
    specialize h x y R.zero
    have h2 : x ≠ R.zero → R.mul x y = R.mul x R.zero → y = R.zero := by
      intro htmp
      intro htmp'
      apply h htmp htmp'
    by_cases h3 : is_zero R x
    · left
      exact h3
    · right
      apply h2 h3 h''

  · rintro h
    intro x y y'
    intro h'
    intro h''
    have h1 : R.mul x (R.add y (R.neg y'))  = R.zero := by
      rw [R.distrib]
      rw (config := {occs := .pos [2]}) [R.mul_comm]
      rw [←inv_assoc]
      rw (config := {occs := .pos [2]}) [R.mul_comm]
      rw [h'']
      apply R.add_inv
    specialize h x (R.add y (R.neg y'))
    have h2 : x = R.zero ∨ R.add y (R.neg y') = R.zero := by
      apply h h1

    rcases h2 with h3 | h3
    exfalso
    exact h' h3
    have h4 : y = y' := by
      apply add_inv_to_zero R y y' h3
    exact h4
