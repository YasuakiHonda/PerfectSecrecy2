/-
Copyright (c) 2025 Yasuaki Honda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yasuaki Honda
-/
/- One-time pad cipher achieves perfect secrecy -/
import PerfectSecrecy2.Defs
import PerfectSecrecy2.KeyReuse
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.BitVec

namespace PerfectSecrecy.OTP

/- BitVec n is used to represent the sets of plain text, cipher text, and keys.-/
variable {n : ℕ} [Fintype (BitVec n)]

/-- One-time pad encryption function -/
def OTP_Enc (n : ℕ) (k : BitVec n) (m : BitVec n) : BitVec n :=
  k ^^^ m

/-- One-time pad decryption function -/
def OTP_Dec (n : ℕ) (k : BitVec n) (c : BitVec n) : BitVec n :=
  k ^^^ c

/-- Correctness of one-time pad encryption and decryption -/
example : correctness (@OTP_Enc n) (@OTP_Dec n) := by
  unfold OTP_Enc OTP_Dec correctness
  intro k m
  simp
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- Uniform distribution over the set of keys -/
noncomputable
def OTP_Gen : PMF (BitVec n) :=
  PMF.uniformOfFintype (BitVec n)

omit [Fintype (BitVec n)] in
/-- Lemma: For any m, k, c ∈ BitVec n, c = Enc(k, m) ↔ k = Dec(c, m) -/
lemma mkc_symm (m k c : (BitVec n)) : c=k^^^m ↔ k=c^^^m := by
  constructor
  · intro hc
    rw [hc, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · intro hk
    rw [hk, BitVec.xor_assoc,BitVec.xor_self, BitVec.xor_zero]

/-- Theorem: One-time pad encryption achieves indistinguishability-based perfect secrecy -/
theorem OTP_is_ind_perfectly_secret :
  ind_perfect_secrecy (OTP_Enc n: BitVec n → BitVec n → BitVec n)
                      (OTP_Gen : PMF (BitVec n)) := by
    intro m₁ m₂ c

    unfold Enc_dist OTP_Gen OTP_Enc
    simp [Bind.bind, PMF.bind_apply, mkc_symm, tsum_ite_eq]



section KeyReuse
open PerfectSecrecy.KeyReuse

/--
BitVec_nontrivial proves that BitVec n is nontrivial when n > 0.
This is essential for demonstrating that the key space has at least two distinct elements,
which is required for the key reuse.
-/
lemma BitVec_nontrivial (n : ℕ) [NeZero n] [Fintype (BitVec n)] : Nontrivial (BitVec n) := by
  have : Nontrivial (Fin (2^n)) := by
    refine Fin.nontrivial_iff_two_le.mpr ?_
    refine Nat.le_self_pow ?_ 2
    exact Ne.symm (NeZero.ne' n)
  exact (BitVec.equivFin (m := n)).toEquiv.nontrivial

/--
This example demonstrates that one-time pad encryption does not achieve perfect secrecy
when the same key is reused for two messages (two-time pad).
It uses the BitVec_nontrivial lemma to show that the key space is nontrivial,
allowing the indistinguishability to be broken.
-/
example (n : ℕ) [NeZero n] [Fintype (BitVec n)] :
    ¬ ind_perfect_secrecy (Enc₂ (OTP_Enc n)) (Gen_reuse OTP_Gen) := by
  refine ind_perfect_secrecy_broken_two_time_same_key (OTP_Enc n) OTP_Gen ?_ ?_
  · intro bn
    unfold OTP_Enc
    rw [Function.Injective]
    intro a₁ a₂
    simp
  · rw [← nontrivial_iff]
    exact BitVec_nontrivial n


/--
This example demonstrates that one-time pad encryption achieves perfect secrecy
even when used for two messages, as long as the keys are generated independently.
It relies on the single-use perfect secrecy theorem (OTP_is_ind_perfectly_secret)
and applies it to the independent key generation scenario.

Note that the only difference between the above and this one is the key generation
algorithm, Gen_reuse in the above and the Gen_indep in the below.
-/
example (n : ℕ) [NeZero n] [Fintype (BitVec n)] :
    ind_perfect_secrecy (Enc₂ (OTP_Enc n)) (Gen_indep OTP_Gen) := by
  refine ind_perfect_secrecy_two_time_indep (OTP_Enc n) OTP_Gen ?_
  exact OTP_is_ind_perfectly_secret

end KeyReuse

end PerfectSecrecy.OTP
