/-
Copyright (c) 2025 Yasuaki Honda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yasuaki Honda
-/
import PerfectSecrecy2.Defs
import Mathlib.Probability.Distributions.Uniform

namespace PerfectSecrecy.Equivalences

open PMF

variable {M K C : Type}

open scoped Classical in
/-- Message being m and cipher text being c are independent.
That is Pr(M=m and C=c) = Pr(M=m)*P(C=c).
This lemma is used in the both directions of the proof.
-/
lemma h_joint_eq_prior_times_enc (Enc : K → M → C) (Gen : PMF K) (m : M) (c : C) (Msg : PMF M) :
    (joint_dist Enc Gen Msg) (m, c) = (Msg m) * (Enc_dist Enc Gen m) c := by
  simp only [joint_dist, Bind.bind, PMF.bind_apply]

  /- h_inner_dist can be used to rewrite the inner sum in the goal.
  -/
  have h_inner_dist (m' : M) : ∑' (a_1 : K), Gen a_1 * (PMF.pure (m', Enc a_1 m')) (m, c) =
      if m'=m then (Enc_dist Enc Gen m) c else 0 := by
        split_ifs with h_eq
        · subst h_eq
          simp only [PMF.pure_apply, Prod.mk.injEq, true_and]
          unfold Enc_dist
          simp only [Bind.bind, PMF.bind_apply, PMF.pure_apply]
        · apply ENNReal.tsum_eq_zero.2
          intro k
          simp only [PMF.pure_apply, Prod.mk.injEq]
          have : (m=m') = False := by exact eq_false fun a ↦ h_eq (id (Eq.symm a))
          rw [this]
          simp only [false_and, if_false, mul_zero]

  conv =>
      lhs; congr; ext m'
      rw [h_inner_dist]

  rw [tsum_eq_single m]
  · simp only [if_true]
  · intro m' h_ne
    have : (m'=m) = False := by exact eq_false h_ne
    rw [this]
    simp only [if_false, mul_zero]

section WithDefaultMessage
variable [Inhabited M]

/-- Theorem: Indistingushability-based perfect secrecy implies
Shannon's definition of perfect secrecy.
-/
theorem shannon_perfect_secrecy_of_ind_perfect_secrecy (Enc : K → M → C) (Gen : PMF K)
    (h_ind : ind_perfect_secrecy Enc Gen) :
    shannon_perfect_secrecy Enc Gen := by

  intro Msg m c h_cipher_nonzero

  -- take the default message from M
  have m0 : M := default
  let P_c := (Enc_dist Enc Gen m0) c

  have h_enc_dist_eq_Pc (m' : M) : (Enc_dist Enc Gen m') c = P_c := by
    exact h_ind m' m0 c


  have h_joint_Pc :
      (joint_dist Enc Gen Msg) (m, c) = (Msg m) * P_c := by
    rw [h_joint_eq_prior_times_enc, h_enc_dist_eq_Pc m]


  have h_cipher_dist_eq_Pc :
      (cipher_dist Enc Gen Msg) c = P_c := by
    -- (cipher_dist Enc Gen Msg) c = ∑' m', (Msg m') * (Enc_dist Enc Gen m') c
    -- = ∑' m', (Msg m') * P_c
    -- = P_c * ∑' m', (Msg m') = P_c * 1 = P_c
    simp only [cipher_dist, Bind.bind, PMF.bind_apply]
    trans ∑' (m' : M), Msg m' * P_c
    · apply tsum_congr; intro m'
      rw [h_enc_dist_eq_Pc m']
    · rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

  have h_Pc_nonzero : P_c ≠ 0 := by
    -- h_cipher_dist_eq_Pc と h_cipher_nonzero を使う
    rw [← h_cipher_dist_eq_Pc]
    exact h_cipher_nonzero


  calc
    posterior Enc Gen Msg m c
      = (joint_dist Enc Gen Msg) (m , c) / ((cipher_dist Enc Gen Msg) c) := by
        unfold posterior
        rw [if_pos h_cipher_nonzero]
    _ = ((Msg m) * P_c) / P_c := by
        rw [h_joint_Pc, h_cipher_dist_eq_Pc]
    _ = (Msg m) := by
        rw [ENNReal.mul_div_cancel_right]
        · exact h_Pc_nonzero
        · exact apply_ne_top (Enc_dist Enc Gen m0) c

end WithDefaultMessage

section FiniteMessageSpace
variable [Fintype M]

/-- Theorem: Shannon's definition of perfect secrecy implies Indistingushable perfect secrecy.
-/
theorem ind_perfect_secrecy_of_shannon_perfect_secrecy (Enc : K → M → C) (Gen : PMF K)
  (h_shannon : shannon_perfect_secrecy Enc Gen) :
    ind_perfect_secrecy Enc Gen := by

    unfold ind_perfect_secrecy
    intro m1 m2 c

    haveI : Nonempty M := ⟨m1⟩
    let Msg : PMF M := PMF.uniformOfFintype M

    have h_Msg_pos (m : M) : Msg m ≠ 0 := by
      rw [PMF.uniformOfFintype_apply]
      refine ENNReal.inv_ne_zero.mpr ?_
      simp

    by_cases h_cipher_zero : (cipher_dist Enc Gen Msg) c = 0

    case pos =>
      /- In this case, both sides are equal because they are zero.
      -/
      have h_enc_zero (m : M) : (Enc_dist Enc Gen m) c = 0 := by
        unfold cipher_dist at h_cipher_zero
        simp only [Bind.bind, PMF.bind_apply] at h_cipher_zero
        have : Msg m * (Enc_dist Enc Gen m) c ≥ 0 := by
          exact zero_le (Msg m * (Enc_dist Enc Gen m) c)
        rw [ENNReal.tsum_eq_zero] at h_cipher_zero
        exact (mul_eq_zero_iff_left (h_Msg_pos m)).mp (h_cipher_zero m)
      rw [h_enc_zero m1, h_enc_zero m2]

    case neg =>
      /- In this case, both sides are equal because they are actually
      (cipher_dist Enc Gen Msg) c, regardless messages being m1 or m2.
      -/
      haveI h_cipher_nonzero : (cipher_dist Enc Gen Msg) c ≠ 0 := h_cipher_zero
      have h_shannon_apply (m : M) : (Enc_dist Enc Gen m) c = (cipher_dist Enc Gen Msg) c := by
        have h_post_eq_prior : posterior Enc Gen Msg m c = Msg m :=
          h_shannon Msg m c h_cipher_nonzero
        have h_post_def : posterior Enc Gen Msg m c =
                ((Msg m) * (Enc_dist Enc Gen m) c) / ((cipher_dist Enc Gen Msg) c) := by
          unfold posterior
          rw [if_pos h_cipher_nonzero]
          rw [h_joint_eq_prior_times_enc]
        rw [h_post_eq_prior] at h_post_def
        rw [ENNReal.eq_div_iff h_cipher_nonzero,mul_comm] at h_post_def
        · refine (ENNReal.mul_left_inj (h_Msg_pos m) ?_).mp ?_
          · exact apply_ne_top Msg m
          · rw [mul_comm]
            rw [h_post_def.symm]
            exact CommMonoid.mul_comm (Msg m) ((cipher_dist Enc Gen Msg) c)
        · exact apply_ne_top (cipher_dist Enc Gen Msg) c
      rw [h_shannon_apply m1, h_shannon_apply m2]



section WithDefaultMessage
variable [Inhabited M]

/-- Main Theorem: Indistinguishability-based perfect secrecy is equivalent to
Shannon's definition of perfect secrecy. -/
theorem ind_perfect_secrecy_equiv_shannon_perfect_secrecy (Enc : K → M → C) (Gen : PMF K) :
  ind_perfect_secrecy Enc Gen ↔ shannon_perfect_secrecy Enc Gen := by
  constructor
  · exact shannon_perfect_secrecy_of_ind_perfect_secrecy Enc Gen
  · exact ind_perfect_secrecy_of_shannon_perfect_secrecy Enc Gen

end WithDefaultMessage

end FiniteMessageSpace

end PerfectSecrecy.Equivalences
