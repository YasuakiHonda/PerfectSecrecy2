/-
Copyright (c) 2025 Yasuaki Honda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yasuaki Honda
-/
import PerfectSecrecy2.Defs

namespace PerfectSecrecy.Equivalences

open PMF

variable {M K C : Type}

section WithDefaultMessage
variable [Inhabited M]

/-- Theorem: Indistinguishability-based perfect secrecy implies
indistinguishability-based perfect secrecy for prior message
distributions. -/
theorem ind_perfect_secrecy_of_ind_prior_perfect_secrecy (Enc : K → M → C) (Gen : PMF K)
    (h_ind : ind_perfect_secrecy Enc Gen) :
    ind_prior_perfect_secrecy Enc Gen := by

  intro Msg1 Msg2 c

  /- We fix an arbitrary message m0 to use as a reference point. We then show that
  for any message m, the probability of c being the encryption of m is equal to the
  probability of c being the encryption of m0.
  -/
  have m0 : M := default
  let P_c := (Enc_dist Enc Gen m0) c

  have h_enc_dist_const (m1 m2 : M) :
      (Enc_dist Enc Gen m1) c = (Enc_dist Enc Gen m2) c :=
    h_ind m1 m2 c

  have h_enc_dist_eq_Pc (m : M) : (Enc_dist Enc Gen m) c = P_c := by
    exact h_enc_dist_const m m0


  /- Next, we show that for any message distribution Msg, the probability of c being
  the encryption of a message generated according to Msg is equal to P_c.
  -/
  have h_Msg_eq_P_c (Msg : PMF M): (cipher_dist Enc Gen Msg) c = P_c := by
    calc
      (cipher_dist Enc Gen Msg) c = ∑' m, (Msg m) * (Enc_dist Enc Gen m) c := by
        unfold cipher_dist
        simp only [Bind.bind, PMF.bind_apply]
      _ = ∑' m, (Msg m) * P_c := by
        congr
        funext m
        exact congrArg (HMul.hMul (Msg m)) (h_ind m m0 c)
      _ = ∑' m, P_c * (Msg m) := by
        congr
        funext m
        rw [mul_comm]
      _ = P_c * ∑' m, (Msg m) := by
        rw [ENNReal.tsum_mul_left]
      _ = P_c * 1 := by
        rw [PMF.tsum_coe]
      _ = P_c := by simp

  /- Finally, we conclude that the probabilities of c being the encryption of messages
  generated according to Msg1 and Msg2 are both equal to P_c, thus proving the
  indistinguishability-based perfect secrecy for prior message distributions.
  -/
  have h_Msg1_eq_P_c : (cipher_dist Enc Gen Msg1) c = P_c := by
    exact h_Msg_eq_P_c Msg1
  have h_Msg2_eq_P_c : (cipher_dist Enc Gen Msg2) c = P_c := by
    exact h_Msg_eq_P_c Msg2

  rw [h_Msg1_eq_P_c, h_Msg2_eq_P_c]

end WithDefaultMessage


section NoDefaultMessage
/-- Theorem: Indistinguishability-based perfect secrecy for prior message
distributions implies indistinguishability-based perfect secrecy. -/
theorem ind_perfect_secrecy_of_ind_prior_perfect_secrecy_rev (Enc : K → M → C) (Gen : PMF K)
    (h_prior_ind : ind_prior_perfect_secrecy Enc Gen) :
    ind_perfect_secrecy Enc Gen := by

  intro m1 m2 c
  /- We construct two message distributions Msg1 and Msg2 that
  assign probability 1 to messages m1 and m2 respectively.
  -/
  let Msg1 : PMF M := PMF.pure m1
  let Msg2 : PMF M := PMF.pure m2

  /- By the assumption of indistinguishability-based perfect secrecy for prior
  message distributions, we have that the probabilities of c being the encryption
  of messages generated according to Msg1 and Msg2 are equal. -/
  have h_cipher_eq : (cipher_dist Enc Gen Msg1) c = (cipher_dist Enc Gen Msg2) c :=
    h_prior_ind Msg1 Msg2 c

  /- Finally, we note that the probabilities of c being the encryption of messages
  generated according to Msg1 and Msg2 reduce to the probabilities of c being
  the encryption of m1 and m2 respectively, thus proving the indistinguishability-based
  perfect secrecy. -/
  have h_pure_relation (m : M) :
      (cipher_dist Enc Gen (PMF.pure m)) c = (Enc_dist Enc Gen m) c := by
    calc
      (cipher_dist Enc Gen (PMF.pure m)) c
        = ∑' m', (PMF.pure m) m' * (Enc_dist Enc Gen m') c := by
          unfold cipher_dist
          simp only [Bind.bind, PMF.bind_apply]
      _ = (PMF.pure m) m * (Enc_dist Enc Gen m) c := by
          rw [PMF.pure_apply]
          simp
      _ = 1 * (Enc_dist Enc Gen m) c := by simp
      _ = (Enc_dist Enc Gen m) c := by simp

  rw [h_pure_relation m1, h_pure_relation m2] at h_cipher_eq
  exact h_cipher_eq

end NoDefaultMessage

section WithDefaultMessage
variable [Inhabited M]

/-- Main Theorem: Indistinguishability-based perfect secrecy is equivalent to
indistinguishability-based perfect secrecy for prior message distributions. -/
theorem ind_perfect_secrecy_equiv_ind_prior_perfect_secrecy (Enc : K → M → C) (Gen : PMF K) :
  ind_perfect_secrecy Enc Gen ↔ ind_prior_perfect_secrecy Enc Gen := by
  constructor
  · exact ind_perfect_secrecy_of_ind_prior_perfect_secrecy Enc Gen
  · exact ind_perfect_secrecy_of_ind_prior_perfect_secrecy_rev Enc Gen

end WithDefaultMessage

end PerfectSecrecy.Equivalences
