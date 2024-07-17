import MIL.Common
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Defs

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

-- Can you guess the names of the theorems that characterize max in a similar way?
#check (max_le)

example : a ≤ max a b := by
  -- apply?
  apply le_max_left
#check le_max_left
#check le_max_right


example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  have h : ∀ x y : ℝ, max x y ≤ max y x := by
    intro x y
    apply max_le
    apply le_max_right
    apply le_max_left
  apply le_antisymm
  · apply h
  · apply h

-- This works
example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · simp
  · simp

/-
-- I was stuck because I couldn't apply min_le_left or right to something
-- of the form min (min a b) c ≤ a
-- so I got the hint that I needed to use le_trans
-- to introduce an intermediate term
-- I think I did something wrong, this is very long
-- and I don't believe it's supposed to be this tedious
-/
example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · show min (min a b) c ≤ min a (min b c)
    apply le_min
    · show min (min a b) c ≤ a
      apply le_trans
      apply min_le_left
      apply min_le_left
    · show min (min a b) c ≤ min b c
      apply le_min
      · apply le_trans
        apply min_le_left
        apply min_le_right
      · apply min_le_right
  · show min a (min b c) ≤ min (min a b) c
    apply le_min
    show min a (min b c) ≤ min a b
    · apply le_min
      · show min a (min b c) ≤ a
        apply min_le_left
      · show min a (min b c) ≤ b
        apply le_trans
        apply min_le_right
        apply min_le_left
    · show min a (min b c) ≤ c
      apply le_trans
      apply min_le_right
      apply min_le_right
-- After reading the solutions apparently this is the way they did it - this sucks
-- And they want me to re-do all that for max (no thanks)

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · apply add_le_add_right
    apply min_le_left
  · apply add_le_add_right
    apply min_le_right

-- This one is nice, apparently it's way shorter than the solution!
-- Also I didn't use sub_add_cancel because the authors did not introduce it at this point
-- and they still used it in their solution ;-;
example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux
  · nth_rw 2 [← add_neg_cancel_right a c, ← add_neg_cancel_right b c]
    linarith [aux (a + c) (b + c) (-c)] -- Worked out on paper


#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  nth_rw 1 [← add_neg_cancel_right a b]
  rw [add_assoc a b (-b), add_comm b (-b), ← add_assoc, ← sub_eq_add_neg]
  linarith [abs_add (a - b) b]

-- Forgot to read, I can use sub_add_cancel_right
-- 3 lines or less! In fact, it's 2 lines
example : |a| - |b| ≤ |a - b| := by
  nth_rw 1 [← sub_add_cancel a b]
  linarith [abs_add (a - b) b]
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  · apply dvd_add
    · -- rw [← mul_assoc, mul_comm y x, mul_assoc]
      -- apply dvd_mul_right
      -- Based on the previous 2 examples I think I'm overcomplicating
      apply dvd_mul_of_dvd_right
      apply dvd_mul_right
    · apply dvd_mul_left
  · have h' : w ^ 2 = w * w := by ring
    rw [h']
    exact Dvd.dvd.mul_right h w

end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

-- Accidentally cheated, apply? gave me the direct theorem
example : Nat.gcd m n = Nat.gcd n m := by
  apply gcd_comm

-- I'll try again, from reading the first line of the solution
-- To be fair I have never seen the formal definition of gcd
-- so I thought this was part of it
example : Nat.gcd m n = Nat.gcd n m := by
  apply dvd_antisymm -- This is a cool trick
  · apply dvd_gcd
    · apply gcd_dvd_right m n
    · apply gcd_dvd_left m n
  · apply dvd_gcd
    · apply gcd_dvd_right n m
    · apply gcd_dvd_left n m

-- Ok I should read a few lines ahead, there was a hint after all ;-;
-- The authors keep adding comments after the challenges
end
