/-
Copyright (c) 2025 Yasuaki Honda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yasuaki Honda
-/
import PerfectSecrecy2.Defs

namespace PerfectSecrecy.KeyReuse

open PMF

variable {M K C : Type}

/-- Two-time encryption algorithm using two (possibly equal) keys. -/
def Enc₂ (Enc : K → M → C) : (K × K) → (M × M) → (C × C)
| (k₁, k₂), (m₁, m₂) => (Enc k₁ m₁, Enc k₂ m₂)


/-- Independent key generation for two-time encryption.
Keys are sampled twice independently from Gen. -/
noncomputable
def Gen_indep (Gen : PMF K) : PMF (K × K) := do
  let k₁ ← Gen
  let k₂ ← Gen
  PMF.pure (k₁, k₂)

/-- Reused-key distribution.
The same key is used for both encryptions. -/
noncomputable
def Gen_reuse (Gen : PMF K) : PMF (K × K) := do
  let k ← Gen
  PMF.pure (k, k)

variable {α β : Type}

/-- Product (independent) distribution of two PMFs. -/
noncomputable
def PMF.prod (μ : PMF α) (ν : PMF β) : PMF (α × β) := do
  let a ← μ
  let b ← ν
  PMF.pure (a, b)

/-- Distribution decomposition lemma for two-time encryption
with independently generated keys. -/
lemma Enc_dist_two_time_indep
  (Enc : K → M → C)
  (Gen : PMF K)
  (m : M × M) :
  Enc_dist (Enc₂ Enc) (Gen_indep Gen) m
    =
  PMF.prod
    (Enc_dist Enc Gen m.1)
    (Enc_dist Enc Gen m.2) := by
  unfold Enc_dist Enc₂ Gen_indep PMF.prod
  ext ⟨c₁, c₂⟩
  cases m with
  | mk m₁ m₂ =>
    simp [Bind.bind]


/-- Perfect secrecy is preserved under two-time encryption
when keys are generated independently. -/
theorem ind_perfect_secrecy_two_time_indep_key
  (Enc : K → M → C)
  (Gen : PMF K) :
  ind_perfect_secrecy Enc Gen →
  ind_perfect_secrecy (Enc₂ Enc) (Gen_indep Gen) := by

  intro h_ind_PS m₁ m₂ c
  -- c : C × C
  -- m₁ m₂ : M × M
  simp [Enc_dist_two_time_indep]
  cases m₁ with
  | mk m₁₁ m₁₂ =>
  cases m₂ with
  | mk m₂₁ m₂₂ =>
  cases c with
  | mk c₁ c₂ =>
    congr 2
    · exact PMF.ext (h_ind_PS m₁₁ m₂₁)
    · exact PMF.ext (h_ind_PS m₁₂ m₂₂)


/-- Perfect secrecy is broken under two-time encryption
when the same key is reused for both encryptions.

Injectivity of Enc k : M → C is required, while
ind_perfect_secrecy Enc Gen is not.

Note that injectivity of Enc k can be derived from ind_perfect_secrecy Enc Gen.

This requires a non-trivial message space, i.e.,
inhabited with at least two different messages -/
theorem ind_perfect_secrecy_broken_two_time_same_key
  (Enc : K → M → C)
  (Gen : PMF K)
  (h_inj_enc : ∀ k : K, Function.Injective (Enc k))
  (hM : ∃ m₁ m₂ : M, m₁ ≠ m₂) :
  ¬ ind_perfect_secrecy (Enc₂ Enc) (Gen_reuse Gen) := by
  intro hPS2
  rcases hM with ⟨m₁, m₂, hneq⟩

  have pmf_exists_ne_zero (Gen : PMF K) : ∃ k : K, Gen k ≠ 0 := by
    by_contra hzero
    push_neg at hzero

    have : (∑' k : K, Gen k) = 0 := by simp [hzero]
    have : (1 : ENNReal) = 0 := by simp [Gen.tsum_coe] at this

    exact one_ne_zero this

  obtain ⟨k, hk⟩ := pmf_exists_ne_zero Gen

  -- choose two plaintext pairs
  let msg₁ := (m₁, m₁)
  let msg₂ : M × M := (m₁, m₂)
  let c : C × C := (Enc k m₁, Enc k m₁)
  have h_msg₁ : msg₁ = (m₁, m₁) := rfl
  have h_msg₂ : msg₂ = (m₁, m₂) := rfl
  have h_c : c = (Enc k m₁, Enc k m₁) := rfl

  have h_pos : (Enc_dist (Enc₂ Enc) (Gen_reuse Gen) msg₁) c ≠ 0 := by
    unfold Enc_dist Enc₂ Gen_reuse
    simp [Bind.bind]
    use k

  have h_zero : (Enc_dist (Enc₂ Enc) (Gen_reuse Gen) msg₂) c = 0 := by
    unfold Enc_dist Enc₂ Gen_reuse
    simp only [Bind.bind, PMF.bind_apply, PMF.pure_apply]
    rw [ENNReal.tsum_eq_zero]
    intro kk
    rw [mul_eq_zero]
    split_ifs with h_c_enc
    · simp
      intro i h_kk_i
      simp [h_kk_i, h_msg₂,h_c] at h_c_enc
      have h_c_enc_2 := h_c_enc.2
      rw [h_c_enc.1] at h_c_enc_2
      apply h_inj_enc at h_c_enc_2
      contradiction
    · right; rfl

  have hPS2m1m2 := hPS2 msg₁ msg₂ c
  simp_all

end PerfectSecrecy.KeyReuse
