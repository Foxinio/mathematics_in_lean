import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

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

theorem min_eq_symm : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

theorem max_eq_symm : max a b = max b a := by
  apply le_antisymm
  . apply max_le
    . apply le_max_right
    . apply le_max_left
  . apply max_le
    . apply le_max_right
    . apply le_max_left

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  . apply le_min
    . apply le_trans
      . apply min_le_left
      . apply min_le_left
    . apply le_min
      . apply le_trans
        . apply min_le_left
        . apply min_le_right
      . apply min_le_right
  . apply le_min
    . apply le_min
      . apply min_le_left
      . apply le_trans
        . apply min_le_right
        . apply min_le_left
    . apply le_trans
      . apply min_le_right
      . apply min_le_right

theorem min_add_aux1 : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  . apply (add_le_add_iff_right c).mpr (min_le_left _ _)
  . apply (add_le_add_iff_right c).mpr (min_le_right _ _)

theorem min_add_aux2 : min (a + c) (b + c) ≤ min a b + c := by
  have h : min (a + c) (b + c) = min (a + c) (b + c) - c + c := by
    rw [sub_add_cancel]
  rw [h]
  apply (add_le_add_iff_right c).mpr
  apply le_min
  . apply sub_left_le_of_le_add
    rw [add_comm c a]
    apply min_le_left
  . apply sub_left_le_of_le_add
    rw [add_comm c b]
    apply min_le_right

theorem min_add : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  . apply min_add_aux1
  . apply min_add_aux2

#check (abs_add_le : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  apply le_abs.mpr
  sorry
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
  sorry
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  sorry
end


