/-
Copyright (c) 2025 Yasuaki Honda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yasuaki Honda
-/
import PerfectSecrecy2.Defs
import Mathlib.Probability.ProbabilityMassFunction.Basic

namespace PerfectSecrecy.GuessingGame

variable {K M C : Type}

open PerfectSecrecy

/--
The guessing game (IND-CPA style) as a PMF over Bool.
A bit `b` is chosen uniformly; the adversary sees an encryption of `m_b`
and outputs a guess `b'`. The outcome is `true` if `b' = b`.
-/
noncomputable
def guessingGame (Enc : K → M → C) (Gen : PMF K) (m0 m1 : M) (A : C → PMF Bool) : PMF Bool := do
  let b ← PMF.bernoulli (1/2) (by norm_num)
  let c ← Enc_dist Enc Gen (if b then m1 else m0)
  let b' ← A c
  pure (b' == b)

/--
If a cipher satisfies `perfect_indistinguishability`, then for any adversary `A`
and any two challenge messages `m0`, `m1`, the adversary wins the guessing game
with probability exactly `1/2` — no better than a random guess.
-/
theorem success_prob_eq_half
  (Enc : K → M → C) (Gen : PMF K)
  (h_pi : perfect_indistinguishability Enc Gen)
  (m0 m1 : M) (A : C → PMF Bool) :
  (guessingGame Enc Gen m0 m1 A) true = 1/2 := by
  -- 1. Expand the definition of guessingGame and PMF bind
  unfold guessingGame
  simp only [Bind.bind]
  simp only [PMF.bind_apply, PMF.bernoulli_apply, Bool.beq_eq_decide_eq]
  simp only [tsum_bool]
  simp only [one_div, cond_false, ENNReal.coe_sub, ENNReal.coe_one, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, ENNReal.coe_inv, ENNReal.coe_ofNat, ENNReal.one_sub_inv_two,
    Bool.false_eq_true, ↓reduceIte, decide_true, Bool.true_eq_false, decide_false, cond_true]

  -- Simplify PMF.pure applied to Bool: (pure true) true = 1, (pure false) true = 0
  have h_pure1 : (pure true : PMF Bool) true = 1 :=
                    PMF.pure_apply true true |>.trans (if_pos rfl)
  have h_pure2 : (pure false : PMF Bool) true = 0 :=
                    PMF.pure_apply false true |>.trans (if_neg (by simp))
  simp_rw [h_pure1, h_pure2]
  simp only [mul_one, mul_zero, add_zero, zero_add]

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
  have h_sum_one : ((Enc_dist Enc Gen m0).bind A) false +
                   ((Enc_dist Enc Gen m0).bind A) true = 1 := by
    rw [← tsum_bool]
    apply PMF.tsum_coe

  rw [h_sum_one]
  rw [mul_one]

end PerfectSecrecy.GuessingGame
