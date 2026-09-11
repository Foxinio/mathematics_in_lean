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
  rintro ⟨b, h'⟩
  rcases h b with ⟨x, h⟩
  apply not_le_of_gt h (h' x)

example : ¬FnHasUb fun x ↦ x := by
  rintro ⟨x, h⟩
  apply (not_forall_not (p:=λ y => x < y)).mpr
  . use x+1
    apply lt_add_of_pos_right; norm_num
  . intro z xltz
    apply not_le_of_gt xltz (h z)

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  unfold Monotone at h
  apply lt_of_not_ge
  intro blea
  apply not_le_of_gt h' (h blea)

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro mf
  unfold Monotone at mf
  have := mf h
  linarith

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro a b aleb
    rfl
  have h' : f 1 ≤ f 0 := le_refl _
  have := @h f monof 1 0 h'
  linarith

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro Oltx
  have := h x
  have xgt0 : x > 0 := by linarith
  apply lt_irrefl _ (this xgt0)

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x Px
  apply h
  use x, Px

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  rintro ⟨x, Px⟩
  apply h x Px

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra nEx
  apply h
  intro x
  by_contra nPx
  apply nEx ⟨x, nPx⟩

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro fa
  rcases h with ⟨x, nPx⟩
  apply nPx (fa x)

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  by_contra
  apply h this

example (h : Q) : ¬¬Q := by
  intro contra
  apply contra h

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro x
  by_contra nEx; apply h
  use x; intro y
  by_contra nfylex ; apply nEx
  use y
  linarith

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push Not at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push Not at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  revert h
  contrapose!
  intro hfa x y xley
  apply hfa _ _ xley

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

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

