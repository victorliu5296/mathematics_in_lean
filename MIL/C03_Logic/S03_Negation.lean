import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro fnlb
  rcases fnlb with ⟨a, fnlba⟩
  rcases h a with ⟨x, hx⟩
  have : a ≤ f x := by exact fnlba x
  linarith

example : ¬FnHasUb fun x ↦ x := by
  -- rintro ⟨a, fnuba⟩
  -- have : ∃x, x > a := by
  --   use (a + 1)
  --   linarith
  -- rcases this with ⟨x, hx⟩
  -- have : x ≤ a := by apply fnuba
  -- linarith

  rintro ⟨a, fnuba⟩
  have : a + 1 ≤ a := by apply fnuba
  linarith

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro a_ge_b
  -- Absurd was not introduced at this point...
  apply absurd h'
  -- exact not_lt_of_ge (h a_ge_b)
  exact not_lt.mpr (h a_ge_b)

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  apply not_le_of_gt at h'
  intro h''
  exact h' (h'' h)

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro h''
  apply absurd h'
  apply not_lt_of_ge
  exact h'' h

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by -- exact monotone_const
    intro a b aleb
    -- exact Preorder.le_refl (f a)
    rfl
  have h' : f 1 ≤ f 0 := le_refl _
  have h'' : (1 : ℝ) ≤ 0 := by
    apply h
    · exact monof
    · exact h'
  linarith only [h'']

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro x_pos
  have : x < x := by
    apply h
    exact x_pos
  linarith

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x Px
  apply h
  use x

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  rintro ⟨x, Px⟩
  exact h x Px

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  absurd h
  intro x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro hx
  rcases h with ⟨x, Px⟩
  exact Px (hx x)

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  by_contra notQ
  absurd h
  exact notQ

example (h : Q) : ¬¬Q := by
  intro notQ
  absurd h
  exact notQ

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra h'
  absurd h
  use a
  intro x
  by_contra h''
  have : f x > a := by exact lt_of_not_ge h''
  exact h' ⟨x, this⟩

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  dsimp only [Monotone] at h
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

example (x : ℝ) (h : ∀ ε > 0, x < ε) (h' : x ≠ 0) : x < 0 := by
  contrapose! h
  use x / 2
  constructor
  · apply lt_of_le_of_ne
    · linarith
    · field_simp
      exact id (Ne.symm h')
  · linarith

example (x : ℝ) (h : ∀ ε > 0, x < ε) (h' : x ≠ 0) : x < 0 := by
  contrapose! h
  use x
  constructor
  · exact lt_of_le_of_ne h (id (Ne.symm h'))
  · exact Preorder.le_refl x

example (x : ℝ) (h : ∀ ε > 0, x < ε) (h' : x ≠ 0) : x < 0 := by
  by_contra! hx
  have := h (x/2) (by positivity) -- or by field_simp
  linarith

example (x : ℝ) (h : ∀ ε > 0, x < ε) (h' : x ≠ 0) : x < 0 := by
  by_contra hx
  have h1 : x ≥ 0 := le_of_not_lt hx
  have h2 : x > 0 := lt_of_le_of_ne h1 (Ne.symm h')
  have h3 := h (x / 2) (half_pos h2)
  linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end
