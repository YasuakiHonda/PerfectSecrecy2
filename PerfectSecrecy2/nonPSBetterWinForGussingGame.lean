/-
Copyright (c) 2025 Yasuaki Honda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yasuaki Honda
-/
import PerfectSecrecy2.Defs
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Basic
import LeanCopilot

open PerfectSecrecy

/-!
# Step 2: Success Probability of the Adversary

This file defines the adversary's strategy based on the reachable message set `S(c)`
and proves the general success probability formula: Pr[Win] = 3/4 - 1/4 * P(X).
-/

variable {K M C : Type} [Fintype K] [Fintype M] [Fintype C]
variable [DecidableEq K] [DecidableEq M] [DecidableEq C]

/--
S(c) is the set of all messages m in M such that there exists a key k
that encrypts m to the given ciphertext c.
-/
def S (Enc : K → M → C) (c : C) : Finset M :=
  Finset.univ.filter (fun m => ∃ k, Enc k m = c)

/--
The specific adversary algorithm from the textbook:
- Takes a ciphertext `c` and two target messages `m0`, `m1`.
- If `m1` is a possible plaintext for `c` (m1 ∈ S(c)), guess bit 0 or 1 uniformly.
- If `m1` is impossible (m1 ∉ S(c)), guess bit 0 (m0).
-/
noncomputable
def proposedAdversary (Enc : K → M → C) (_m0 m1 : M) (c : C) : PMF Bool :=
  if m1 ∈ S Enc c then
    PMF.bernoulli (1/2) (by norm_num)
  else
    PMF.pure false

/--
The guessing game experiment (IND-CPA style).
-/
noncomputable
def guessingGame (Enc : K → M → C) (Gen : PMF K) (m0 m1 : M) (A : C → PMF Bool) : PMF Bool := do
  let b ← PMF.bernoulli (1/2) (by norm_num)
  let c ← Enc_dist Enc Gen (if b then m1 else m0)
  let b' ← A c
  pure (b' == b)

omit [Fintype C] [DecidableEq K] [DecidableEq M] in
/-- Lemma: If c is generated from m1, then m1 is always in the set S(c) -/
lemma m1_in_S_of_Enc_m1 (Enc : K → M → C) (k : K) (m1 : M) :
  m1 ∈ S Enc (Enc k m1) := by
  simp [S]

/-- The probability that `pure true` evaluates to `true` is 1. -/
lemma h_pure1 : (pure true : PMF Bool) true = 1 :=
                  PMF.pure_apply true true |>.trans (if_pos rfl)
/-- The probability that `pure false` evaluates to `true` is 0. -/
lemma h_pure2 : (pure false : PMF Bool) true = 0 :=
                  PMF.pure_apply false true |>.trans (if_neg (by simp))

omit [Fintype C] [DecidableEq K] in
/--
Step 2 Theorem:
The probability that the proposed adversary wins the game is 3/4 - 1/4 * P(X),
where P_X is the probability that m1 is in S(c) given that m0 was encrypted.
-/
theorem success_prob_general_formula
  (Enc : K → M → C) (Gen : PMF K) (m0 m1 : M) :
      let A := proposedAdversary Enc m0 m1
      let P_X := (Gen.bind fun k => PMF.pure (m1 ∈ S Enc (Enc k m0))) true
    (guessingGame Enc Gen m0 m1 A) true = 3/4 - 1/4 * P_X := by

  intro A P_X

  -- Step 2.1: Expand the game definition into a sum over b, k, and c.
  -- We use tsum_bool to split the case b = true and b = false.
  suffices h_split : (guessingGame Enc Gen m0 m1 A) true =
    1/2 * ((Enc_dist Enc Gen m1).bind A) true +
    1/2 * ((Enc_dist Enc Gen m0).bind A) false by
      rw [h_split]
      -- [Intermediate Goal]: Calculate the two conditional probabilities


      -- Step 2.2: Analyze the probability when b = true (m1 was encrypted).
      -- Since m1 is always in S(Enc k m1), the adversary always guesses uniformly.
      have h_b_true : ((Enc_dist Enc Gen m1).bind A) true = 1/2 := by
        -- [Intermediate Goal]: Show m1 ∈ S(Enc k m1) and A(c) true = 1/2
        simp only [PMF.bind_apply, A, proposedAdversary]
        conv_lhs =>
          arg 1; ext a; arg 2;
          dsimp
          rw [show (if m1 ∈ S Enc a then PMF.bernoulli (1 / 2) _ else PMF.pure false) true =
            if m1 ∈ S Enc a then PMF.bernoulli (1 / 2) _ true else PMF.pure false true
            by split_ifs <;> rfl]
        simp only [one_div, PMF.bernoulli_apply, cond_true, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, ENNReal.coe_inv, ENNReal.coe_ofNat, PMF.pure_apply, Bool.true_eq_false,
          ↓reduceIte, mul_ite, mul_zero]
        have h_ite : ∀ a, (if m1 ∈ S Enc a then (Enc_dist Enc Gen m1) a * 2⁻¹ else 0) =
                        (Enc_dist Enc Gen m1) a * 2⁻¹ := by
          intro a
          by_cases h_in : m1 ∈ S Enc a
          · rw [if_pos h_in]
          · rw [if_neg h_in]
            simp only [zero_eq_mul, ENNReal.inv_eq_zero, ENNReal.ofNat_ne_top, or_false]
            -- Show that (Enc_dist Enc Gen m1) a = 0 when m1 ∉ S Enc a
            contrapose! h_in
            simp [Enc_dist, Bind.bind, PMF.bind_apply, PMF.pure_apply] at h_in
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
            obtain ⟨k, hk⟩ := h_in
            use k
            exact hk.1.symm

        simp_rw [h_ite]
        rw [ENNReal.tsum_mul_right]
        rw [(Enc_dist Enc Gen m1).tsum_coe, one_mul]

      -- Step 2.3: Analyze the probability when b = false (m0 was encrypted).
      -- This depends on the event X (m1 ∈ S(c)).
      -- P(Win | b=0) = 1/2 * P(X) + 1 * (1 - P(X)) = 1 - 1/2 * P(X).
      have h_b_false : ((Enc_dist Enc Gen m0).bind A) false = 1 - 1/2 * P_X := by
        -- [Intermediate Goal]: Express A(c) false using an indicator function of S(c)
        -- suffices h_indicator : ∀ c, A c false = 1 - 1/2 * (if m1 ∈ S Enc c then 1 else 0)
        simp only [PMF.bind_apply, A, proposedAdversary]
        conv_lhs =>
          arg 1; ext a; arg 2;
          dsimp
          rw [show (if m1 ∈ S Enc a then PMF.bernoulli (1 / 2) _ else PMF.pure false) false =
            if m1 ∈ S Enc a then PMF.bernoulli (1 / 2) _ false else PMF.pure false false
            by split_ifs <;> rfl]
        simp only [one_div, PMF.bernoulli_apply, cond_false, ENNReal.coe_sub, ENNReal.coe_one,
          ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_inv, ENNReal.coe_ofNat,
          ENNReal.one_sub_inv_two, PMF.pure_apply, ↓reduceIte, mul_ite, mul_one]

        let loss_term (a : C) := if m1 ∈ S Enc a then (Enc_dist Enc Gen m0) a * 2⁻¹ else 0
        let succ_term (a : C) := if m1 ∈ S Enc a then (Enc_dist Enc Gen m0) a * 2⁻¹
                                                 else (Enc_dist Enc Gen m0) a
        -- Step 2.3.2: Prove that succ_term + loss_term = (Enc_dist m0) a for each ciphertext
        have h_pointwise : ∀ a, succ_term a + loss_term a = (Enc_dist Enc Gen m0) a := by
          intro a
          by_cases hX : m1 ∈ S Enc a <;> simp [hX, succ_term, loss_term]
          -- Case m1 ∈ S(a): (p * 1/2) + (p * 1/2) = p
          · ring_nf
            rw [mul_assoc]
            have : (2:ENNReal)⁻¹ * 2 = 1 := by
              rw [ENNReal.inv_mul_cancel]
              · norm_num
              · norm_num
            rw [this,mul_one]
          -- Step 2.3.3: Sum both sides. Using tsum_add for ENNReal (always valid for non-negative)
        have h_sum_add : ∑' a, succ_term a + ∑' a, loss_term a = 1 := by
          rw [← ENNReal.tsum_add]
          simp only [h_pointwise]
          rw [PMF.tsum_coe]

        -- Step 2.3.4: Relate the loss_term sum to P_X
        have zero_two: 0=0 * (2:ENNReal)⁻¹ := by rw [zero_mul]
        have h_loss_PX : ∑' a, loss_term a = 2⁻¹ * P_X := by
          simp only [loss_term, P_X]
          simp only [PMF.bind_apply, PMF.pure_apply, eq_iff_iff, true_iff, mul_ite,mul_one,
                    mul_zero]
          simp_rw [S]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          conv_lhs =>
            arg 1; ext a; arg 3;
            rw [zero_two]
          conv_lhs =>
            arg 1; ext a;
            rw [← ite_mul]
          rw [ENNReal.tsum_mul_right, mul_comm]
          congr 1
          simp_rw [Enc_dist, Bind.bind, PMF.bind_apply, PMF.pure_apply]

          have h_push (i : C) : (if ∃ k, Enc k m1 = i then ∑' (a : K),
              Gen a * (@ite ENNReal (i = Enc a m0) (Classical.propDecidable (i = Enc a m0)) 1 0)
              else 0) =
              ∑' (a : K), if ∃ k, Enc k m1 = i then Gen a *
              (@ite ENNReal (i = Enc a m0) (Classical.propDecidable (i = Enc a m0)) 1 0)
              else 0 := by
            split_ifs with h
            · rfl -- case: P i is true
            · simp -- case: P i is false, sum of 0 is 0
          simp_rw [h_push]
          rw [ENNReal.tsum_comm]

          simp only [mul_ite, mul_one, mul_zero, ← ite_and]
          apply tsum_congr; intro k
          rw [tsum_eq_single (Enc k m0)]
          · simp only [and_true]
          · intro b' hb'
            grind

        apply ENNReal.eq_sub_of_add_eq
        · apply ENNReal.mul_ne_top
          · norm_num
          · apply ne_top_of_le_ne_top (b:=1)
            · norm_num
            · apply PMF.coe_le_one
        · convert h_sum_add using 1
          rw [h_loss_PX]

      have nnreal_success_calc (p : NNReal) (hp : p ≤ 1) :
          (1/2 : NNReal) * (1/2) + 1/2 * (1 - 1/2 * p) = 3/4 - 1/4 * p := by
        rw [mul_tsub]
        ring_nf
        rw [← add_tsub_assoc_of_le]
        · norm_num
        · calc
            p * (1 / 4) ≤ 1 * (1 / 4) := by gcongr
            _= 1/4 := by norm_num
            _≤ 1/2 := by gcongr; norm_num

      have h_finite : P_X ≠ ⊤ := by apply PMF.apply_ne_top -- PMFなら常に有限
      let p := P_X.toNNReal
      have hp_coe : P_X = ↑p := (ENNReal.coe_toNNReal h_finite).symm
      have P_X_le_one : P_X ≤ 1 := by unfold P_X; apply PMF.coe_le_one
      have p_le_one : p ≤ 1 := by exact (WithTop.le_coe hp_coe).mp P_X_le_one

      -- Result: 1/2 * (1/2) + 1/2 * (1 - 1/2 * P_X) = 1/4 + 1/2 - 1/4 * P_X = 3/4 - 1/4 * P_X.
      have h_final_calc : 1/2 * (1/2 : ENNReal) + 1/2 * (1 - 1/2 * P_X) = 3/4 - 1/4 * P_X := by
        -- [Intermediate Goal]: Perform ENNReal arithmetic safely
        rw [hp_coe]
        have h_final : (1/2 : ENNReal) * (1/2) + 1/2 * (1 - 1/2 * p) = (3/4) - (1/4) * p := by
          have h34: (3/4:ENNReal)=(3/4:NNReal) := by norm_num
          have h12: (1/2:ENNReal)=(1/2:NNReal) := by norm_num
          have h14: (1/4:ENNReal)=(1/4:NNReal) := by norm_num
          have h1: (1:ENNReal)=(1:NNReal) := by norm_num
          rw [h14,h34,h12,← ENNReal.coe_mul,← ENNReal.coe_mul,← ENNReal.coe_mul]
          nth_rw 1 [h1,← ENNReal.coe_sub,← ENNReal.coe_sub,← ENNReal.coe_mul,← ENNReal.coe_add]
          congr
          exact nnreal_success_calc p p_le_one

        exact h_final
      rw [h_b_true, h_b_false, h_final_calc]

  -- Proof of the decomposition (h_split):
  -- [Goal here]:
  -- ⊢ (guessingGame Enc Gen m0 m1 A) true =
  --   1/2 * ((Gen.bind fun k => PMF.pure (Enc k m1)).bind A) true +
  --   1/2 * ((Gen.bind fun k => PMF.pure (Enc k m0)).bind A) false
  -- This involves unfolding the 'do' block (guessingGame) and splitting the sum over b.
  unfold guessingGame
  -- Step 2.5.1: Expand all monadic binds into summations.
  -- We'll have three summations: over b (Bool), c (C), and b' (Bool).
  simp only [Bind.bind, PMF.bind_apply, PMF.bernoulli_apply, Bool.beq_eq_decide_eq]
  simp only [tsum_bool]

  -- Step 2.5.2: Split the outermost sum over b using tsum_bool.
  -- This creates the 1/2 coefficients and separates m1 and m0 paths.
  simp only [Bool.cond_true, Bool.cond_false, ite_true, one_div]
  rw [← mul_add]
  simp only [ENNReal.coe_sub, ENNReal.coe_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    ENNReal.coe_inv, ENNReal.coe_ofNat, ENNReal.one_sub_inv_two, Bool.false_eq_true, ↓reduceIte,
    decide_true, Bool.true_eq_false, decide_false]
  rw [h_pure1, h_pure2]
  simp only [mul_one, mul_zero, add_zero, zero_add]
  ring
