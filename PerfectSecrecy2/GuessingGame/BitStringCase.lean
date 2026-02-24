/-
Copyright (c) 2025 Yasuaki Honda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yasuaki Honda
-/

import PerfectSecrecy2.Defs
import PerfectSecrecy2.GuessingGame.Defs
import PerfectSecrecy2.GuessingGame.SmallKeySpace
import PerfectSecrecy2.GuessingGame.ENNRealCalc
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.SetTheory.Ordinal.Arithmetic

namespace PerfectSecrecy.GuessingGame

open PMF

variable {K M C : Type} [Fintype K] [Fintype M]
variable [DecidableEq M] [DecidableEq C]

/-- The probability that a randomly chosen message `m1` is reachable from ciphertext `c`,
    where `c` is produced by encrypting `m0` under a random key.
    Formally: `Pr[c ← Enc_K(m0); m1 ∈ S Enc c]`. -/
noncomputable
def prob_m1_in_S (Enc : K → M → C) (Gen : PMF K) (m0 m1 : M) : ENNReal :=
  (do let c ← Enc_dist Enc Gen m0
      PMF.pure (if m1 ∈ S Enc c then (1:ENNReal) else 0)) 1

/-- `prob_m1_in_S` is always finite (not ⊤), since it is a probability value. -/
lemma prob_m1_in_S_ne_top (Enc : K → M → C) (Gen : PMF K) (m0 m1 : M) :
    prob_m1_in_S Enc Gen m0 m1 ≠ ⊤ := by
  unfold prob_m1_in_S
  apply PMF.apply_ne_top


omit [DecidableEq M] in
/-- The number of plaintexts reachable from ciphertext `c` is at most `|K|`,
    provided each encryption function `Enc k` is injective.
    Proof: construct an injection from `S Enc c` into `K` by mapping each
    reachable message to a witness key. -/
lemma S_card_le_key_card (Enc : K → M → C) (c : C)
    (h_inj : ∀ k, Function.Injective (Enc k)) :
    (S Enc c).card ≤ Fintype.card K := by
  -- Map each reachable message to a witness key via Classical.choose
  let f : {m // m ∈ S Enc c} → K :=
    fun ⟨m, hm⟩ => Classical.choose ((Finset.mem_filter.mp hm).2)
  have hf_inj : Function.Injective f := by
    intro ⟨m1, hm1⟩ ⟨m2, hm2⟩ heq
    simp only [f] at heq
    have hk1 := Classical.choose_spec ((Finset.mem_filter.mp hm1).2)
    have hk2 := Classical.choose_spec ((Finset.mem_filter.mp hm2).2)
    rw [← heq] at hk2
    -- The same key maps both m1 and m2 to c; injectivity of Enc k gives m1 = m2
    have := h_inj _ (hk1.trans hk2.symm)
    simp [this]
  calc (S Enc c).card
      = Fintype.card {m // m ∈ S Enc c} := by simp [Fintype.card_coe]
    _ ≤ Fintype.card K := Fintype.card_le_of_injective f hf_inj

/-- The average over all `m1` of `prob_in_S Enc Gen m0 m1` is at most `1/2`,
    given that `|K| * 2 = |M|`. This follows from `|S Enc c| ≤ |K| = |M| / 2`. -/
lemma avg_prob_in_S_le (Enc : K → M → C) (Gen : PMF K) (m0 : M)
    (h_inj : ∀ k, Function.Injective (Enc k))
    (h_card : Fintype.card K * 2 = Fintype.card M) :
    (∑ m1, prob_m1_in_S Enc Gen m0 m1) / Fintype.card M ≤ 1/2 := by
  -- Rewrite the sum over m1 as a weighted sum over ciphertexts c
  have sum_eq : ∑' m1, prob_m1_in_S Enc Gen m0 m1
              = ∑' c, (Enc_dist Enc Gen m0) c * (Finset.card (S Enc c) : ENNReal) := by
    simp only [prob_m1_in_S, Bind.bind, PMF.bind_apply, PMF.pure_apply]
    simp only [left_eq_ite_iff, one_ne_zero, imp_false, Decidable.not_not, mul_ite, mul_one,
      mul_zero]
    -- ENNReal.tsum_comm: swap the order of summation over m1 and c
    rw [ENNReal.tsum_comm]
    congr 1; ext c
    simp only [tsum_fintype, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    rw [mul_comm]

  -- Bound |S Enc c| ≤ |K| for each c
  have sum_le : ∑' c, (Enc_dist Enc Gen m0) c * (Finset.card (S Enc c) : ENNReal)
              ≤ ∑' c, (Enc_dist Enc Gen m0) c * (Fintype.card K : ENNReal) := by
    apply ENNReal.tsum_le_tsum
    intro c
    gcongr
    apply S_card_le_key_card
    exact fun k ↦ h_inj k
  -- The weighted sum with constant |K| equals |K| (since Gen is a distribution)
  have sum_eq_card : ∑' c, (Enc_dist Enc Gen m0) c * (Fintype.card K : ENNReal)
                   = Fintype.card K := by
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe,one_mul]
  rw [tsum_eq_sum] at sum_eq
  · rw [sum_eq]
    rw [ENNReal.div_le_iff]
    · calc ∑' c, (Enc_dist Enc Gen m0) c * (Finset.card (S Enc c) : ENNReal)
        ≤ Fintype.card K := by rw [← sum_eq_card]; exact sum_le
      _ = (Fintype.card M : ENNReal) / 2 := by
          -- Use h_card: |K| * 2 = |M|, so |K| = |M| / 2
          have : (Fintype.card K : ENNReal) * 2 = Fintype.card M := by
            exact_mod_cast h_card
          rw [← this]
          rw [ENNReal.div_eq_inv_mul]
          nth_rw 2 [mul_comm]
          rw [← mul_assoc]
          rw [ENNReal.inv_mul_cancel]
          · rw [one_mul]
          · norm_num
          · norm_num
      _ = _ := by
          rw [ENNReal.div_eq_inv_mul,ENNReal.div_eq_inv_mul,mul_one]
    · norm_num
      haveI : Nonempty M := ⟨m0⟩
      exact Fintype.card_pos.ne'
    · norm_num
  · norm_num

/-- If the average of a function over a finite nonempty type is at most `bound`,
    then there exists an element where the function value is at most `bound`.
    (NNReal version, used as a stepping stone for the ENNReal version.) -/
lemma exists_le_of_avg_le_NNReal {α : Type*} [Fintype α] [Nonempty α]
    (f : α → NNReal) (bound : NNReal)
    (h_avg : (∑ a, f a) / Fintype.card α ≤ bound) :
    ∃ a, f a ≤ bound := by
  by_contra h_not
  push_neg at h_not
  -- If every value exceeds bound, the sum exceeds bound * |α|
  have sum_gt : ∑ a, f a > bound * Fintype.card α := by
    calc ∑ a, f a
        = ∑ a, f a := rfl
      _ > ∑ a, bound := by
          apply Finset.sum_lt_sum
          · intro a _
            exact le_of_lt (h_not a)
          · obtain ⟨a⟩ := ‹Nonempty α›
            use a
            constructor
            · simp only [Finset.mem_univ]
            · exact h_not a
      _ = bound * Fintype.card α := by
          rw [Finset.sum_const, Finset.card_univ]
          ring
  -- Therefore the average exceeds bound, contradicting h_avg
  have : (∑ a, f a) / Fintype.card α > bound := by
    have card_pos : (0:NNReal) < Fintype.card α := by
      norm_cast
      exact Fintype.card_pos
    refine (lt_div_iff₀ card_pos).mpr sum_gt
  have h1 : bound < (∑ a, f a) / Fintype.card α := by
    exact this
  have h2 : bound < bound := by
    exact Std.lt_of_lt_of_le this h_avg
  exact (lt_self_iff_false bound).mp h2

/-- If the average of a finite-valued ENNReal function over a finite nonempty type
    is at most `bound`, then there exists an element where the value is at most `bound`. -/
lemma exists_le_of_avg_le {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ENNReal)
    (bound : ENNReal)
    (h_avg : (∑ a, f a) / Fintype.card α ≤ bound)
    (hf : ∀ x, f x ≠ ⊤)
    (hbound : bound ≠ ⊤) :
    ∃ a, f a ≤ bound := by
  -- lift: convert ENNReal hypothesis to NNReal to apply the NNReal version
  lift bound to NNReal using hbound
  let g : α → NNReal := fun a => (f a).toNNReal
  have h_fg : ∀ a, f a = ↑(g a) := fun a => (ENNReal.coe_toNNReal (hf a)).symm
  simp_rw [h_fg] at h_avg ⊢
  simp_rw [ENNReal.coe_le_coe]
  rw [← ENNReal.coe_finset_sum] at h_avg
  have h_card_ne_zero : (Fintype.card α : NNReal) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true]
  -- Rewrite ENNReal division as NNReal division to apply exists_le_of_avg_le_NNReal
  have h_div : (↑(∑ a, g a) : ENNReal) / Fintype.card α =
                    ↑((∑ a, g a) / (Fintype.card α : NNReal)) := by
    norm_cast
  rw [h_div] at h_avg
  rw [ENNReal.coe_le_coe] at h_avg
  exact exists_le_of_avg_le_NNReal g bound h_avg

/-- Convenience lemma: the average of `prob_m1_in_S` over all `m1` is at most `1/2`. -/
lemma avg_le_half (Enc : K → M → C) (Gen : PMF K) (m0 : M)
    (h_inj : ∀ k, Function.Injective (Enc k))
    (h_card : Fintype.card K * 2 = Fintype.card M) :
    (∑ m1, (prob_m1_in_S Enc Gen m0 m1)) / Fintype.card M ≤ 1/2 := by
  exact avg_prob_in_S_le Enc Gen m0 h_inj h_card

omit [DecidableEq M] in
/-- Both `K` and `M` are nonempty: `K` because `Gen` has nonempty support,
    and `M` because `|M| = 2 * |K| > 0`. -/
lemma K_M_Nonempty (Gen : PMF K)
    (h_card : Fintype.card K * 2 = Fintype.card M) :
    Nonempty M ∧ Nonempty K := by
  haveI h1 : Nonempty K := by
    obtain ⟨k, _⟩ := Gen.support_nonempty
    exact ⟨k⟩
  haveI h2 : Nonempty M := by
    have hK : 0 < Fintype.card K := Fintype.card_pos
    have hM : 0 < Fintype.card M := by
      calc 0 < Fintype.card K * 2 := by omega
          _ = Fintype.card M := h_card
    exact Fintype.card_pos_iff.mp hM
  exact ⟨h2, h1⟩

/-- When `|K| * 2 = |M|` and each `Enc k` is injective, there exist messages
    `m0`, `m1` such that `e Enc Gen m0 m1 ≥ 1/2`.
    This follows from an averaging argument: the average reachability probability
    is at most `1/2`, so some `m1` achieves reachability at most `1/2`,
    which means `e ≥ 1/2` for that pair. -/
lemma exists_e_ge_half (Enc : K → M → C) (Gen : PMF K)
    (h_inj : ∀ k, Function.Injective (Enc k))
    (h_card : Fintype.card K * 2 = Fintype.card M) :
    ∃ m0 m1, e Enc Gen m0 m1 ≥ 1/2 := by
  haveI : Nonempty M := (K_M_Nonempty Gen h_card).left
  obtain ⟨m0⟩ : Nonempty M := inferInstance
  let prob_in_S (m1 : M) : ENNReal := prob_m1_in_S Enc Gen m0 m1

  have avg_bound : (∑ m1, prob_in_S m1) / Fintype.card M ≤ 1/2 := by
    exact avg_le_half Enc Gen m0 h_inj h_card

  -- By averaging, there exists m1 with reachability probability ≤ 1/2
  have exists_good : ∃ m1, prob_in_S m1 ≤ 1/2 := by
    apply exists_le_of_avg_le
    · exact avg_bound
    · intro m1
      exact prob_m1_in_S_ne_top Enc Gen m0 m1
    · norm_num

  obtain ⟨m1, h_prob⟩ := exists_good
  use m0, m1

  -- e and prob_in_S are complementary: e + prob_in_S = 1
  have h_relation : e Enc Gen m0 m1 = 1 - prob_in_S m1 := by
    have h_sum : e Enc Gen m0 m1 + prob_in_S m1 = 1 := by
      unfold e prob_in_S prob_m1_in_S
      simp only [Bind.bind, PMF.bind_apply, PMF.pure_apply]
      rw [← ENNReal.tsum_add]
      conv_rhs => rw [← PMF.tsum_coe (Enc_dist Enc Gen m0)]
      congr 1; ext c
      rw [← mul_add]
      split_ifs <;> simp_all
    -- ENNReal.eq_sub_of_add_eq: derive x = 1 - y from x + y = 1
    apply ENNReal.eq_sub_of_add_eq
    · unfold prob_in_S
      exact PMF.apply_ne_top _ _
    · exact h_sum

  rw [h_relation]
  -- Since prob_in_S m1 ≤ 1/2, we have 1 - prob_in_S m1 ≥ 1/2
  apply ENNReal.le_sub_of_add_le_right
  · exact PMF.apply_ne_top _ _
  · rw [add_comm]
    rw [← ENNReal.le_sub_iff_add_le_right]
    · norm_num
      apply ENNReal.mul_le_of_le_div
      exact h_prob
    · norm_num
    · norm_num

/-- Main theorem: when `|K| * 2 = |M|` and each `Enc k` is injective,
    there exist challenge messages `m0`, `m1` such that the proposed adversary
    wins the guessing game with probability at least `5/8`. -/
theorem guessing_game_five_eighths
    (Enc : K → M → C) (Gen : PMF K)
    (h_inj : ∀ k, Function.Injective (Enc k))
    (h_card : Fintype.card K * 2 = Fintype.card M) :
    ∃ m0 m1, (guessingGame Enc Gen m0 m1 (proposedAdversary Enc m0 m1)) true ≥ 5/8 := by
  obtain ⟨m0, m1, h_e⟩ := exists_e_ge_half Enc Gen h_inj h_card
  use m0, m1
  haveI : Inhabited M := ⟨m0⟩
  -- Apply the success probability formula: win prob = 1/2 + e/4
  rw [guessing_game_success_prob]
  -- Rewrite 5/8 = 1/2 + 1/8 and reduce to showing 1/8 ≤ e/4
  rw [formula58, ge_iff_le]
  rw [ENNReal.add_le_add_iff_left]
  · rw [ge_iff_le] at h_e
    -- Rewrite 1/8 = (1/2)/4 and apply monotonicity of division
    rw [formula124]
    apply ENNReal.div_le_div_right
    exact h_e
  · norm_num

end PerfectSecrecy.GuessingGame
