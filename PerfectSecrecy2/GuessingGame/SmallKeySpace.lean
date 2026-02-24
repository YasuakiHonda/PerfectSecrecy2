/-
Copyright (c) 2025 Yasuaki Honda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yasuaki Honda
-/

import PerfectSecrecy2.Defs
import PerfectSecrecy2.GuessingGame.Defs
import PerfectSecrecy2.GuessingGame.ENNRealCalc
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace PerfectSecrecy.GuessingGame

open PMF

variable {K M C : Type} [Fintype K] [Fintype M]
variable [DecidableEq M] [DecidableEq C]



/-- The Bernoulli(1/2) distribution assigns probability 1/2 to each Boolean value. -/
lemma bernoulli_half (b : Bool) :
    (PMF.bernoulli (1/2) (by norm_num)) b = 1/2 := by
  simp [PMF.bernoulli_apply]
  cases b <;> simp

/-- If a ciphertext `c` has nonzero probability of arising from encrypting `m1`,
    then `m1 ∈ S Enc c`, and the proposed adversary outputs `true` with probability 1/2. -/
lemma proposedAdversary_true_eq (Enc : K → M → C) (Gen : PMF K) (m0 m1 : M) (c : C)
    (hc : (Enc_dist Enc Gen m1) c ≠ 0) :
    (proposedAdversary Enc m0 m1 c) true = 1/2 := by
  -- Show m1 ∈ S Enc c by contraposition:
  -- if no key maps m1 to c, then the weighted sum over keys is zero, contradicting hc.
  have h_m1_in_S : m1 ∈ S Enc c := by
    rw [Enc_dist] at hc
    simp only [Bind.bind, PMF.bind_apply, PMF.pure_apply] at hc
    rw [S]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    -- Convert tsum to Finset.sum to use Finset.sum_eq_zero_iff
    rw [tsum_fintype] at hc
    by_contra h_not
    push_neg at h_not
    apply hc
    -- Finset.sum_eq_zero_iff: a sum over a finset is 0 iff each term is 0
    rw [Finset.sum_eq_zero_iff]
    intro k _
    by_cases h : c = Enc k m1
    · exfalso
      exact h_not k h.symm
    · simp [h]
  rw [proposedAdversary, if_pos h_m1_in_S]
  rw [bernoulli_half true]

/-- The proposed adversary outputs `false` with probability 1/2 if `m1 ∈ S Enc c`
    (uniform guess), or with probability 1 if `m1 ∉ S Enc c` (always correct). -/
lemma proposedAdversary_false_eq (Enc : K → M → C) (m0 m1 : M) (c : C) :
    (proposedAdversary Enc m0 m1 c) false =
    if m1 ∈ S Enc c then 1/2 else 1 := by
  rw [proposedAdversary]
  split_ifs with h
  · rw [bernoulli_half false]
  · simp [PMF.pure_apply]

/-- When `b = false` (i.e., `m0` was encrypted), the conditional success probability
    of the proposed adversary is `1/2 + e/2`. -/
lemma success_prob_false (Enc : K → M → C) (Gen : PMF K) (m0 m1 : M) :
    ∑' a, (Enc_dist Enc Gen m0) a * (proposedAdversary Enc m0 m1 a) false
                 = 1/2 + (e Enc Gen m0 m1)/2 := by
  -- Rewrite adversary's false-output probability using proposedAdversary_false_eq
  have rewrite_sum : ∑' c, (Enc_dist Enc Gen m0) c * (proposedAdversary Enc m0 m1 c) false
                  = ∑' c, (Enc_dist Enc Gen m0) c *
                    (if m1 ∈ S Enc c then 1/2 else 1) := by
    congr; ext c
    rw [proposedAdversary_false_eq]
  rw [rewrite_sum]
  -- Split the sum into the m1-reachable part (×1/2) and unreachable part (×1)
  have split_cases : ∑' c, (Enc_dist Enc Gen m0) c * (if m1 ∈ S Enc c then 1/2 else 1)
                  = ∑' c, (Enc_dist Enc Gen m0) c * (if m1 ∈ S Enc c then 1/2 else 0)
                  + ∑' c, (Enc_dist Enc Gen m0) c * (if m1 ∈ S Enc c then 0 else 1) := by
    conv_lhs => congr; ext c
                rw [show (if m1 ∈ S Enc c then (1/2 : ENNReal) else 1)
                        = (if m1 ∈ S Enc c then 1/2 else 0) + (if m1 ∈ S Enc c then 0 else 1) by
                  split_ifs <;> simp]
    simp only [mul_add, ENNReal.tsum_add]
  rw [split_cases]
  -- The unreachable part equals e by definition
  have second_term : ∑' c, (Enc_dist Enc Gen m0) c * (if m1 ∈ S Enc c then 0 else 1)
                  = e Enc Gen m0 m1 := by
    rw [e]
    simp only [Bind.bind, PMF.bind_apply, PMF.pure_apply]
    congr; ext c; congr 1
    split_ifs with _ h1 h2 <;> simp_all
  -- The reachable part equals (1 - e) * (1/2),
  -- using the complement identity: Pr[reachable] = 1 - e
  have first_term : ∑' c, (Enc_dist Enc Gen m0) c * (if m1 ∈ S Enc c then 1/2 else 0)
                  = (1 - e Enc Gen m0 m1) * (1/2) := by
    -- Factor out 1/2 from the indicator
    have factor_out : ∑' c, (Enc_dist Enc Gen m0) c * (if m1 ∈ S Enc c then 1/2 else 0)
                    = ∑' c, (Enc_dist Enc Gen m0) c * (if m1 ∈ S Enc c then 1 else 0) * (1/2)
                    := by
      congr; ext c
      split_ifs <;> simp
    rw [factor_out]
    -- ENNReal.tsum_mul_right: pull the constant (1/2) outside the tsum
    rw [ENNReal.tsum_mul_right]
    congr
    -- Show Pr[reachable] + e = 1, then deduce Pr[reachable] = 1 - e
    have sum_complement : ∑' c, (Enc_dist Enc Gen m0) c * (if m1 ∈ S Enc c then 1 else 0)
                        = 1 - e Enc Gen m0 m1 := by
      have total : ∑' c, (Enc_dist Enc Gen m0) c * (if m1 ∈ S Enc c then 1 else 0)
                + ∑' c, (Enc_dist Enc Gen m0) c * (if m1 ∈ S Enc c then 0 else 1) = 1 := by
        rw [← ENNReal.tsum_add]
        conv_rhs => rw [← PMF.tsum_coe (Enc_dist Enc Gen m0)]
        congr; ext c
        rw [← mul_add]
        split_ifs <;> simp
      rw [second_term] at total
      -- ENNReal.sub_eq_of_eq_add: derive x = 1 - e from x + e = 1
      rw [ENNReal.sub_eq_of_eq_add (e_not_top Enc Gen m0 m1) total.symm]
    rw [sum_complement]

  rw [first_term,second_term]
  -- Conclude using the ENNReal arithmetic identity: (1-e)*(1/2) + e = 1/2 + e/2
  apply formula2
  exact e_le_one Enc Gen m0 m1

/-- When `b = true` (i.e., `m1` was encrypted), the conditional success probability
    of the proposed adversary is `1/2`, since `m1` is always reachable from its own encryption. -/
lemma success_prob_true (Enc : K → M → C) (Gen : PMF K) (m0 m1 : M) :
    ∑' a, (Enc_dist Enc Gen m1) a * (proposedAdversary Enc m0 m1 a) true = 1/2 := by
  -- Replace adversary probability with 1/2:
  -- if Enc_dist c = 0 the term vanishes; otherwise use proposedAdversary_true_eq
  have rewrite_sum_true (Enc : K → M → C) (Gen : PMF K) (m0 m1 : M) :
      ∑' c, (Enc_dist Enc Gen m1) c * (proposedAdversary Enc m0 m1 c) true
          = ∑' c, (Enc_dist Enc Gen m1) c * (1/2) := by
    congr; ext c
    by_cases h : (Enc_dist Enc Gen m1) c = 0
    · simp [h]
    · congr 1
      exact proposedAdversary_true_eq Enc Gen m0 m1 c h

  rw [rewrite_sum_true]
  -- ENNReal.tsum_mul_right + PMF.tsum_coe: ∑ p(c) * (1/2) = (1/2) * ∑ p(c) = 1/2
  rw [ENNReal.tsum_mul_right, tsum_coe, one_mul]

/-- Main theorem: the proposed adversary wins the guessing game with probability exactly
    `1/2 + e/4`, where `e = Pr[c ← Enc_K(m0); m1 ∉ S Enc c]`. -/
theorem guessing_game_success_prob
    (Enc : K → M → C) (Gen : PMF K) (m0 m1 : M) :
    (guessingGame Enc Gen m0 m1 (proposedAdversary Enc m0 m1)) true
    = 1/2 + (e Enc Gen m0 m1)/4 := by
  rw [guessingGame]
  simp only [Bind.bind, PMF.bind_apply, PMF.pure_apply]
  -- tsum_bool: split the outer sum over b ∈ {false, true} into two terms
  rw [tsum_bool]
  rw [bernoulli_half false, bernoulli_half true]
  -- Expand the inner sum over b' ∈ {false, true} using tsum_fintype,
  -- so that each branch can be simplified by simp
  conv_lhs =>
    arg 1;arg 2; arg 1; ext c; arg 2;
    rw [tsum_fintype]
  conv_lhs =>
    arg 2;arg 2; arg 1; ext c; arg 2;
    rw [tsum_fintype]

  simp only [↓reduceIte, beq_true, Bool.true_eq, mul_ite, mul_one, mul_zero,
    Fintype.univ_bool, Finset.sum_ite_eq', Finset.mem_insert, Finset.mem_singleton,
    or_false, Bool.false_eq_true, beq_false, Bool.not_eq_eq_eq_not,
    Bool.not_true, or_true]

  -- Apply the two conditional probability lemmas and conclude with formula3
  rw [success_prob_true, success_prob_false]
  rw [mul_add, add_assoc]
  nth_rw 2 [add_comm]
  apply formula3

/-- Corollary: the proposed adversary wins the guessing game with probability at least `1/2`
    for any encryption scheme. -/
theorem guessing_game_advantage
    (Enc : K → M → C) (Gen : PMF K) (m0 m1 : M) :
    (guessingGame Enc Gen m0 m1 (proposedAdversary Enc m0 m1)) true ≥ 1/2 := by
  rw [guessing_game_success_prob]
  simp only [one_div, ge_iff_le, self_le_add_right]

end PerfectSecrecy.GuessingGame
