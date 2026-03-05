/-
Copyright (c) 2025 Yasuaki Honda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yasuaki Honda
-/
import PerfectSecrecy2.Defs
import PerfectSecrecy2.GuessingGame.Defs
import Mathlib.Probability.ProbabilityMassFunction.Basic

namespace PerfectSecrecy.GuessingGame

variable {K M C : Type}

open PerfectSecrecy.GuessingGame

/--
If a cipher satisfies `perfect_indistinguishability`, then for any adversary `A`
and any two challenge messages `m0`, `m1`, the adversary wins the guessing game
with probability exactly `1/2` — no better than a random guess.
-/
theorem success_prob_eq_half
  (Enc : K → M → C) (Gen : PMF K)
  (h_pi : perfect_indistinguishability Enc Gen)
  (m0 m1 : M) (A : C → PMF Bit) :
  (guessingGame Enc Gen m0 m1 A) true = 1/2 := by
  -- 1. Expand the definition of guessingGame and PMF bind
  unfold guessingGame
  simp only [Bind.bind,PMF.bind_apply, randomBit_apply, Bool.beq_eq_decide_eq]
  simp only [tsum_bit]
  simp only [↓reduceIte, Fin.isValue, decide_true, PMF.pure_apply, mul_one, one_ne_zero,
    decide_false, Bool.true_eq_false, mul_zero, add_zero, zero_ne_one, zero_add]

  -- 2. Reassemble into (Enc_dist ...).bind A form
  rw [← PMF.bind_apply, ← PMF.bind_apply]

  -- 3. Apply perfect indistinguishability to equate the two distributions
  have h_pi_m1_m0_A := h_pi m1 m0 A
  simp only [bind] at h_pi_m1_m0_A
  have : (fun c => A c) = A := by rfl
  rw [this] at h_pi_m1_m0_A
  rw [h_pi_m1_m0_A]
  rw [← mul_add]

  -- The two outputs of A sum to 1 (total probability), so (1/2) * 1 = 1/2
  have h_sum_one : ((Enc_dist Enc Gen m0).bind A) 0 +
                   ((Enc_dist Enc Gen m0).bind A) 1 = 1 := by
    rw [← tsum_bit]
    apply PMF.tsum_coe

  rw [h_sum_one]
  rw [mul_one]

end PerfectSecrecy.GuessingGame
