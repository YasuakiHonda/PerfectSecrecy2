/-
Copyright (c) 2025 Yasuaki Honda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yasuaki Honda
-/

import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv

namespace PerfectSecrecy.GuessingGame

/-- Helper lemma: `(1/2) * A ≠ ⊤` whenever `A ≤ 1`. -/
lemma half_A_ne_top (A : ENNReal) (h_A_le_one : A ≤ 1) : (1/2:ENNReal) * A ≠ ⊤ :=
  ENNReal.mul_ne_top (by simp) (ne_top_of_le_ne_top (by norm_num) h_A_le_one)

/-- Helper lemma: `(1/2 : ENNReal) ≠ ⊤`. -/
lemma half_ne_top : (1/2:ENNReal) ≠ ⊤ := by norm_num

/--
Arithmetic identity in ENNReal:
`1 / 2 * (1 - A) + A = 1 / 2 + A / 2`, valid when `A ≤ 1`.
-/
lemma formula1 (A : ENNReal) (h_A_le_one : A ≤ 1) : 1 / 2 * (1 - A) + A = 1 / 2 + A / 2 := by
  have hA : A ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) h_A_le_one
  rw [← ENNReal.toReal_eq_toReal_iff'
    (ENNReal.Finiteness.add_ne_top
      (ENNReal.mul_ne_top (by simp) (ENNReal.sub_ne_top (by norm_num))) hA)
    (ENNReal.Finiteness.add_ne_top (by simp) (ENNReal.div_ne_top hA (by simp))),
    ENNReal.toReal_add
      (ENNReal.mul_ne_top (by simp) (ENNReal.sub_ne_top (by norm_num))) hA,
    ENNReal.toReal_mul,
    ENNReal.toReal_sub_of_le h_A_le_one (by norm_num),
    ENNReal.toReal_add (by simp) (ENNReal.div_ne_top hA (by simp)),
    ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num; ring

/--
Arithmetic identity in ENNReal:
`(1 - A) * (1 / 2) + A = 1 / 2 + A / 2`, valid when `A ≤ 1`.
-/
lemma formula2 (A : ENNReal) (h_A_le_one : A ≤ 1) : (1 - A) * (1 / 2) + A = 1 / 2 + A / 2 := by
  rw [mul_comm]
  exact formula1 A h_A_le_one

private lemma half_sq_ne_top : (1/2:ENNReal) * (1/2) ≠ ⊤ :=
  ENNReal.mul_ne_top (by simp) (by simp)

/--
Arithmetic identity in ENNReal:
`1 / 2 * (1 / 2) + (1 / 2 * (1 / 2) + 1 / 2 * (A / 2)) = 1 / 2 + A / 4`.
-/
lemma formula3 (A : ENNReal) :
    1 / 2 * (1 / 2) + (1 / 2 * (1 / 2) + 1 / 2 * (A / 2)) = 1 / 2 + A / 4 := by
  rcases eq_or_ne A ⊤ with rfl | hA
  · simp [ENNReal.top_div_of_lt_top (by norm_num : (2:ENNReal) < ⊤),
          ENNReal.top_div_of_lt_top (by norm_num : (4:ENNReal) < ⊤)]
  rw [← ENNReal.toReal_eq_toReal_iff'
    (ENNReal.Finiteness.add_ne_top half_sq_ne_top
      (ENNReal.Finiteness.add_ne_top half_sq_ne_top
        (ENNReal.mul_ne_top (by simp) (ENNReal.div_ne_top hA (by simp)))))
    (ENNReal.Finiteness.add_ne_top (by simp) (ENNReal.div_ne_top hA (by simp))),
    ENNReal.toReal_add half_sq_ne_top
      (ENNReal.Finiteness.add_ne_top half_sq_ne_top
        (ENNReal.mul_ne_top (by simp) (ENNReal.div_ne_top hA (by simp)))),
    ENNReal.toReal_add half_sq_ne_top
      (ENNReal.mul_ne_top (by simp) (ENNReal.div_ne_top hA (by simp))),
    ENNReal.toReal_add (by simp) (ENNReal.div_ne_top hA (by simp)),
    ENNReal.toReal_mul (a := 1/2) (b := 1/2),
    ENNReal.toReal_mul (a := 1/2) (b := A/2),
    ENNReal.toReal_div (a := A) (b := 2),
    ENNReal.toReal_div (a := A) (b := 4),
    ENNReal.toReal_ofNat]
  norm_num; ring

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
