import Mathlib.Data.Int.LeastGreatest

structure myRing (α : Type) where
  add : α → α → α
  mul : α → α → α
  zero : α
  one : α
  neg : α → α
  add_comm : ∀ x y : α, add x y = add y x
  mul_comm : ∀ x y : α, mul x y = mul y x
  add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z)
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  distrib : ∀ x y z : α, mul x (add y z) = add (mul x y) (mul x z)
  add_zero : ∀ x : α, add x zero = x
  add_inv : ∀ x : α, add x (neg x) = zero
  mul_ident : ∀ x : α, mul x one = x

structure myOrderedRing (α : Type) extends myRing α where
  P : Set α -- α → Prop
  P_nonempty : P.Nonempty -- ∃ x : α , P α
  P_add : ∀ a b : α, a ∈ P → b ∈ P → add a b ∈ P
  P_mul : ∀ a b : α, a ∈ P → b ∈ P → mul a b ∈ P
  trichotomy1 : zero ∉ P
  trichotomy2 : ∀ a , a ∈ P → neg a ∉ P
  trichotomy3 : ∀ a , a ∉ P → a ≠ zero → neg a ∈ P

def myRing.sub {α : Type} (R : myRing α) (x y : α) : α :=
  R.add x (R.neg y)

def myOrderedRing.lt {α : Type} (R : myOrderedRing α) (a b : α) : Prop :=
  R.add a (R.neg b) ∈ R.P

def myOrderedRing.le {α : Type} (R : myOrderedRing α) (a b : α) : Prop :=
  R.add a (R.neg b) ∈ R.P ∨ a = b

def myOrderedRing.gt {α : Type} (R : myOrderedRing α) (a b : α) : Prop := -- b > a
  R.add b (R.neg a) ∈ R.P

def myOrderedRing.ge {α : Type} (R : myOrderedRing α) (a b : α) : Prop := -- b > a
  R.add b (R.neg a) ∈ R.P ∨ a = b

structure WellOrderedRing (α : Type) extends myOrderedRing α where
  well_ordered : ∀ (S : Set α), S.Nonempty → S ⊆ tomyOrderedRing.P →
  ∃ m ∈ S, ∀ s ∈ S, myOrderedRing.le tomyOrderedRing s m

-- Define the integer ring
def intRing : myRing Int :={
  add := Int.add,
  mul := Int.mul,
  zero := 0,
  one := 1,
  neg := Int.neg,
  add_comm := Int.add_comm,
  mul_comm := Int.mul_comm,
  add_assoc := Int.add_assoc,
  mul_assoc := Int.mul_assoc,
  distrib := Int.mul_add,
  add_zero := Int.add_zero,
  add_inv := Int.add_right_neg,
  mul_ident := Int.mul_one
}

def intP : Set Int :=
  {x | x > 0}

def orderedIntRing : myOrderedRing Int := {
  tomyRing := intRing,
  P := intP,
  P_nonempty := ⟨1, by simp [intP]⟩,
  P_add := by
    intro a b ha hb
    simp [intP] at *
    exact Int.add_pos ha hb

  P_mul := by
    intro a b ha hb
    simp [intP] at *
    exact Int.mul_pos ha hb

  trichotomy1 := by
    simp [intP]
    exact Int.zero_lt_one

  trichotomy2 := by
    intro a ha
    simp [intP] at *
    have ha' : -a < 0 := by
      exact Int.neg_neg_of_pos ha
    exact Int.le_of_lt ha'

  trichotomy3 := by
    intro a ha hza
    simp [intP] at *
    have hza' : 0 ≠ a := by
      rw [ne_comm]
      exact hza
    have h : a < 0 := by
      exact lt_of_le_of_ne' ha hza'
    apply Int.neg_pos_of_neg
    exact h
}

def wellOrderedIntRing : WellOrderedRing Int := {
  tomyOrderedRing := orderedIntRing,
  well_ordered := by
    intro S hS hP

    have Hinh : ∃ (z : ℤ), z ∈ S := by
      exact hS

    have Hbdd : ∃ (b : ℤ), ∀ (z : ℤ), z ∈ S → b ≤ z := ⟨0, by
      intro z hz
      have z_pos : z ∈ orderedIntRing.P := by
        exact hP hz
      have zero_le_pos : ∀ z ∈ orderedIntRing.P, 0 ≤ z := by
        intro z' hzP
        simp [intP] at hzP
        exact Int.le_of_lt hzP
      exact zero_le_pos z z_pos
    ⟩

    obtain ⟨lb, lb_in_S, is_least⟩ := Int.exists_least_of_bdd Hbdd Hinh
    use lb
    apply And.intro
    · exact lb_in_S

    intro s s_in_S
    unfold myOrderedRing.le
    have Hle := is_least s s_in_S
    by_cases h_eq : lb = s
    · right
      exact h_eq.symm
    left
    have Hlt : lb < s := by
      exact lt_of_le_of_ne Hle h_eq

    have tmp : orderedIntRing.P = intP := by
      rfl
    rw [tmp]
    simp [intP]

    have tmp2 : orderedIntRing.neg = Int.neg := by
      rfl
    rw [tmp2]

    have tmp3 : orderedIntRing.add = Int.add := by
      rfl
    rw [tmp3]

    simp

    have tmp4 : lb.neg = -lb := by
      rfl
    rw [tmp4]

    simp
    exact Hlt
}
