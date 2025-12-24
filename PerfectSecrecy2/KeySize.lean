/-
Copyright (c) 2025 Yasuaki Honda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yasuaki Honda
-/
import PerfectSecrecy2.Defs

namespace PerfectSecrecy.KeySize

open PMF


variable {M K C : Type}
variable [Fintype M] [Inhabited M] [DecidableEq M]
variable [Fintype K]
variable [DecidableEq C]

/-- Theorem: In any symmetric encryption scheme (Enc, Dec, Gen) that achieves
indistinguishability-based perfect secrecy and correctness, the size of the key space K
must be at least as large as the size of the message space M. -/
theorem K_GE_M (Enc : K → M → C) (Dec : K → C → M) (Gen : PMF K)
      (h_correct : correctness Enc Dec)
      (h_ind_PS : ind_perfect_secrecy Enc Gen) :
    Fintype.card K ≥ Fintype.card M := by

  have pmf_of_fintype_exists_ne_zero {T : Type} [Fintype T] (Gen : PMF T) : ∃ t : T, Gen t ≠ 0 := by
    by_contra hzero
    push_neg at hzero
    have : (∑' t : T, Gen t) = 0 := by simp [hzero]
    have : (1 : ENNReal) = 0 := by simp [Gen.tsum_coe] at this
    exact one_ne_zero this

  by_contra K_M
  push_neg at K_M

  /- We fix an arbitrary message m₀ ∈ M and an arbitrary key k₀ ∈ K.
  We then consider the ciphertext c₀ = Enc(k₀, m₀). Next, we define the set S₀
  of all messages that can be obtained by decrypting c₀ with every possible key in K.
  Since the size of K is smaller than the size of M, there must exist at least one
  message m₁ ∈ M that is not in S₀.
  -/
  have m₀:M := default
  obtain ⟨k₀, hk₀⟩:= pmf_of_fintype_exists_ne_zero Gen
  -- have k₀:K := default
  let c₀:C := Enc k₀ m₀
  have hc₀ : c₀=Enc k₀ m₀ := by rfl

  let f : K → M := fun k => Dec k c₀
  -- let S₀ := {m:M | ∃k:K, m=Dec k c₀}
  let S₀ := Finset.image f Finset.univ

  have S₀_le_K: S₀.card ≤ @Fintype.elems.card K := by
    exact Finset.card_image_le

  have S₀_lt_M : S₀.card < Fintype.card M := by
    exact Nat.lt_of_le_of_lt S₀_le_K K_M

  obtain ⟨m₁, hm₁⟩ : ∃m₁:M, ¬ m₁ ∈ S₀ := by
    by_contra hc
    push_neg at hc
    have : S₀=Finset.univ := by
      exact Finset.eq_univ_iff_forall.mpr hc
    simp_rw [this] at S₀_lt_M
    exact (lt_self_iff_false Finset.univ.card).mp S₀_lt_M

  /- Now, we analyze the probabilities of c₀ being the encryption of m₀ and m₁.
  Since m₁ is not in S₀, it means that for every key k ∈ K, decrypting c₀ with k
  does not yield m₁.
  -/
  have Enc_m1_ne_c₀ : ∀ k : K, Enc k m₁ ≠ c₀ := by
    intro k
    by_contra contra
    apply hm₁
    have correct:= h_correct k m₁
    rw [contra] at correct
    rw [Finset.mem_image]
    use k
    constructor
    · exact Finset.mem_univ k
    · exact correct

  /- We show that the probability of c₀ being the encryption of m₁ is zero,
  while the probability of c₀ being the encryption of m₀ is positive. This contradicts
  the assumption of indistinguishability-based perfect secrecy.
  -/
  have Enc_m1_zero : (Enc_dist Enc Gen m₁) c₀ = 0 := by
    simp only [Enc_dist, Bind.bind, PMF.bind_apply, PMF.pure_apply]
    rw [tsum_eq_sum]
    · apply Finset.sum_eq_zero
      intro k _
      have : c₀ ≠ Enc k m₁ := by exact fun a => Enc_m1_ne_c₀ k (id (Eq.symm a))
      rw [if_neg this]
      simp
    · intro k _
      have : c₀ ≠ Enc k m₁ := by exact fun a => Enc_m1_ne_c₀ k (id (Eq.symm a))
      rw [if_neg this]
      simp
    · exact Finset.empty

  have Enc_m0_pos : (Enc_dist Enc Gen m₀) c₀ > 0 := by
    simp only [Enc_dist, Bind.bind, PMF.bind_apply, PMF.pure_apply]
    have single_le_tsum: (fun a => Gen a * if c₀ = Enc a m₀ then 1 else 0) k₀
      ≤ (∑' (a : K), Gen a * if c₀ = Enc a m₀ then 1 else 0) := by
      exact ENNReal.le_tsum k₀
    have single_gt_zero: 0<(fun a => Gen a * if c₀ = Enc a m₀ then 1 else 0) k₀ := by
      simp_all [c₀]
      exact (apply_pos_iff Gen k₀).mpr hk₀
    apply lt_of_lt_of_le single_gt_zero
    simp_all

  /- Finally, we reach a contradiction by showing that the probabilities of c₀
  being the encryption of m₀ and m₁ are equal due to perfect secrecy,
  which contradicts our earlier findings.
  -/
  have ps := h_ind_PS m₀ m₁ c₀
  simp_all

end PerfectSecrecy.KeySize
