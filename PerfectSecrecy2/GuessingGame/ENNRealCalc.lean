/-
Copyright (c) 2025 Yasuaki Honda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yasuaki Honda
-/

import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv

namespace PerfectSecrecy.GuessingGame

/-- Helper lemma: `(1/2) * A ≠ ⊤` whenever `A ≤ 1`. -/
lemma half_A_ne_top (A : ENNReal) (h_A_le_one : A ≤ 1) : (1/2:ENNReal) * A ≠ ⊤ := by
  rw [ne_eq]
  rw [ENNReal.mul_eq_top]
  push_neg
  norm_num
  push_neg
  intro h
  rw [h] at h_A_le_one
  contradiction

/-- Helper lemma: `(1/2 : ENNReal) ≠ ⊤`. -/
lemma half_ne_top : (1/2:ENNReal) ≠ ⊤ := by norm_num

/--
Arithmetic identity in ENNReal:
`1 / 2 * (1 - A) + A = 1 / 2 + A / 2`, valid when `A ≤ 1`.
-/
lemma formula1 (A : ENNReal) (h_A_le_one : A ≤ 1) : 1 / 2 * (1 - A) + A = 1 / 2 + A / 2 := by
  rw [ENNReal.mul_sub,mul_one]
  · rw [ENNReal.sub_add_eq_add_sub]
    · rw [ENNReal.sub_eq_of_eq_add_rev]
      · exact half_A_ne_top A h_A_le_one
      · nth_rw 2 [add_comm]
        rw [add_assoc]
        have : A / 2 = 1 /2 * A := by
          have h1: A / 2 = A / 2 * 1 := by
            rw [mul_one]
          rw [h1]
          rw [ENNReal.mul_comm_div, mul_comm]
        rw [this]
        rw [← mul_add]
        have : A + A = 2 * A := by
          exact Eq.symm (two_mul (A))
        rw [this]
        rw [← mul_assoc]
        simp only [one_div]
        rw [ENNReal.inv_mul_cancel,one_mul]
        · norm_num
        · norm_num
    · have : (1 / 2:ENNReal) * 1 = 1 / 2 := by rw [mul_one]
      nth_rw 2 [← this]
      rw [ENNReal.mul_le_mul_iff_right]
      · exact h_A_le_one
      · norm_num
      · norm_num
    · exact half_A_ne_top A h_A_le_one
  · exact fun a a_1 ↦ half_ne_top

/--
Arithmetic identity in ENNReal:
`(1 - A) * (1 / 2) + A = 1 / 2 + A / 2`, valid when `A ≤ 1`.
-/
lemma formula2 (A : ENNReal) (h_A_le_one : A ≤ 1) : (1 - A) * (1 / 2) + A = 1 / 2 + A / 2 := by
  rw [mul_comm]
  exact formula1 A h_A_le_one

/--
Arithmetic identity in ENNReal:
`1 / 2 * (1 / 2) + (1 / 2 * (1 / 2) + 1 / 2 * (A / 2)) = 1 / 2 + A / 4`.
-/
lemma formula3 (A : ENNReal) :
        1 / 2 * (1 / 2) + (1 / 2 * (1 / 2) + 1 / 2 * (A / 2)) = 1 / 2 + A / 4 := by
  simp only [one_div]
  rw [← add_assoc]
  rw [← mul_add]
  rw [ENNReal.inv_two_add_inv_two, mul_one]
  rw [ENNReal.add_right_inj]
  · rw [ENNReal.div_eq_inv_mul,ENNReal.div_eq_inv_mul]
    rw [← mul_assoc]
    have : (1 / 2:ENNReal) = 2⁻¹ := by
      rw [← ENNReal.inv_div]
      · rw [div_one]
      · norm_num
      · norm_num
    rw [← this]
    rw [← ENNReal.mul_div_mul_comm] <;> norm_num
  · norm_num

/-- Arithmetic identity: `(5/8 : ENNReal) = 1/2 + 1/8`. -/
lemma formula58 : (5/8 : ENNReal) = 1/2 + 1/8 := by
  -- Cast to NNReal to use norm_cast and ring
  have : (5/8 : ENNReal)=(5/8 : NNReal) := by
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_div, ENNReal.coe_ofNat]
  rw [this]
  have : (1/2 : ENNReal)=(1/2: NNReal) := by
    simp only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_inv,
      ENNReal.coe_ofNat]
  rw [this]
  have : (1/8 : ENNReal)=(1/8: NNReal) := by
    simp only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_inv,
      ENNReal.coe_ofNat]
  rw [this]
  norm_cast; ring

/-- Arithmetic identity: `(1/8 : ENNReal) = (1/2) / 4`. -/
lemma formula124 : (1/8:ENNReal) = (1/2)/4 := by
  -- Cast to NNReal to use norm_cast and ring
  have : (1/8:ENNReal) = (1/8:NNReal) := by
    simp only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_inv,
      ENNReal.coe_ofNat]
  rw [this]
  have : (1/2 : ENNReal)=(1/2: NNReal) := by
    simp only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_inv,
      ENNReal.coe_ofNat]
  rw [this]
  have : (4 : ENNReal)=(4: NNReal) := by rfl
  rw [this]
  rw [← ENNReal.coe_div]
  · norm_cast
    ring
  · norm_num

end PerfectSecrecy.GuessingGame
