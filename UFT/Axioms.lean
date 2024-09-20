import Mathlib.Data.Set.Lattice

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
