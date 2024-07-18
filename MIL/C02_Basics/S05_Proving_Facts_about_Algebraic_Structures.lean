import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat'
  · apply le_inf
    · apply inf_le_right
    · apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · apply le_trans
      apply inf_le_left
      apply inf_le_left
    · apply le_inf
      · apply le_trans
        apply inf_le_left
        apply inf_le_right
      · apply inf_le_right
  · apply le_inf
    · apply le_inf
      · apply inf_le_left
      · apply le_trans
        apply inf_le_right
        apply inf_le_left
    · apply le_trans
      apply inf_le_right
      apply inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat'
  · apply sup_le
    apply le_sup_right
    apply le_sup_left

-- My original solution using le_trans' from messing around
example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      · apply le_sup_left
      · apply le_trans'
        apply le_sup_right
        apply le_sup_left
    · apply le_trans'
      apply le_sup_right
      apply le_sup_right
  · apply sup_le
    · apply le_trans'
      apply le_sup_left
      apply le_sup_left
    · apply sup_le
      · apply le_trans'
        apply le_sup_left
        apply le_sup_right
      · apply le_sup_right

-- Trying the authors' method using @
example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      · apply le_sup_left
      · apply le_trans
        apply @le_sup_left _ _ y z
        apply le_sup_right
    · apply le_trans
      apply @le_sup_right _ _ y z
      apply le_sup_right
  · apply sup_le
    · apply le_trans
      apply @le_sup_left _ _ x y
      apply le_sup_left
    · apply sup_le
      · apply le_trans
        apply @le_sup_right _ _ x y
        apply le_sup_left
      · apply le_sup_right

-- simp works on both, gg
theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  simp

example : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left
  · apply le_inf
    · apply le_refl
    · apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le
    · apply le_refl
    · apply inf_le_left
  · apply le_sup_left

#check inf_sup_self
#check sup_inf_self

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

/-
Attempts at finding a finite non-distributive lattice.
Of course, it was mentioned earlier that max/min on reals is distributive,
so I will not try it. Looking at the previous examples of lattices,
I suspect some kind of sets would work since they can easily be
non-trivially finite unlike vector spaces. Otherwise GCD/LCD
might work, but I am sure boolean does not work since AND behaves
just like min and OR behaves just like max on the reals.
As for the topologies, I am not familiar with the theory on what it is
formally, so I am likely missing out because I suspect those might have
counterexamples.
1. Sets {0}, {1}, {0, 1} with ordering ⊆, inf ∩, sup ∪
Try {0} ∪ {1} ∩ {0,1} = {0} ∪ {1} = {0,1}
({0} ∪ {1}) ∩ ({0} ∪ {0,1}) = {0,1} ∩ {0,1} = {0,1}
does not work. Probably too much overlap, I'll try this:
2. Sets 0:={0}, 1:={1}, 02:={0,2}
0 ∪ 1 ∩ 02 = 0 ∪ ∅ = 0
(0 ∪ 1) ∩ (0 ∪ 02) = 01 ∩ 02 = 0
3. Sets 0:={0}, 1:={1}, 2:={2}
0 ∪ 1 ∩ 2 = 0 ∪ ∅ = 0
(0 ∪ 1) ∩ (0 ∪ 2) = 01 ∩ 02 = 0
Ok, I suspect this won't work so simply.
I'll try GCD/LCD instead.
Actually, I realize that natural numbers can be factored using the
fundamental theorem of arithmetic and can therefore be represented as
multisets, or even sets with each prime factor with duplicates
numbered according to the exponent in the factorization, so it is
equivalent to set union and intersection.
I'll probably have to look up some counterexamples as I couldn't find
any myself.
-/

-- Scrapped, last part needs cases which I haven't learnt about yet
-- example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
--   rw [h]
--   apply le_antisymm
--   · apply sup_le
--     · apply le_trans'
--       apply le_sup_left
--       apply le_inf
--       · apply le_sup_left
--       · apply le_refl
--     · apply le_trans'
--       apply le_sup_right
--       apply le_inf
--       · apply le_trans
--         apply inf_le_left
--         apply le_sup_right
--       · apply inf_le_right
--   ·

-- Had to look at solution for hints, you use rw only with commutativity theorem
-- I thought you weren't supposed to use it since we did not name the theorem
-- when we proved it but I guess anything is free game
example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h]
  rw [inf_comm (a ⊔ b) a, absorb1]
  rw [inf_comm (a ⊔ b) c, h] -- This is the only way to expand the expression, I didn't think of it in the moment
  rw [← sup_assoc, inf_comm c, absorb2, inf_comm]

-- I am almost sure that the proof is identical
-- just with sup and inf swapped (and absorb1 and absorb2)
example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h]
  rw [sup_comm (a ⊓ b) a, absorb2]
  rw [sup_comm (a ⊓ b) c, h]
  rw [← inf_assoc, sup_comm c, absorb1, sup_comm]
-- Indeed, it worked flawlessly! I didn't even have to look at the output
end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  -- simp [h] -- works
  have h' : a ≤ a + (b - a) := by
    rw [add_sub_cancel]
    exact h

-- Having trouble with using add_le_add_left
  have h'' : -a + a ≤ -a + (a + (b - a)) := by
    apply add_le_add_left h' (-a)

  rw [neg_add_self, add_comm, add_sub_cancel, ← sub_eq_add_neg] at h''
  exact h''

-- Let's try that again
example (h : a ≤ b) : 0 ≤ b - a := by
  rw [← neg_add_self a, sub_eq_add_neg, add_comm b]
  apply add_le_add_left
  exact h
-- Much better

example (h: 0 ≤ b - a) : a ≤ b := by
  rw [← add_zero a, ← sub_add_cancel b a, add_comm (b - a)]
  apply add_le_add_left h

-- I'm guessing you need to use the previous 2 examples to prove this
-- On top of factoring to be able to use mul_pos
example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  rw [← add_zero (a * c), ← add_neg_cancel_left (a * c) (b * c)]
  apply add_le_add_left
  rw [add_comm, ← sub_eq_add_neg, ← sub_mul]
  apply mul_nonneg
  · rw [← neg_add_self a, sub_eq_add_neg, add_comm b]
    apply add_le_add_left
    exact h
  · exact h'

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

-- dist_triangle x y x : dist x x ≤ dist x y + dist y x
-- 0 ≤ 2 * dist x y → 0 ≤ dist x y
example (x y : X) : 0 ≤ dist x y := by
  have h := dist_triangle x y x
  rw [dist_self x, dist_comm y x] at h
  rw [← two_mul] at h
  linarith
end
