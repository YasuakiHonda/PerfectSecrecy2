/-
Copyright (c) 2025 Yasuaki Honda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yasuaki Honda
-/
import PerfectSecrecy2.Defs

namespace PerfectSecrecy.Equivalences

open PMF

variable {M K C : Type}


-- The following proofs assume the definitions provided in Def.lean

/--
Forward direction: Point-wise indistinguishability implies
indistinguishability against any probabilistic adversary.
-/
theorem ind_perfect_secrecy_imp_perfect_indistinguishability
    (Enc : K → M → C) (Gen : PMF K) :
    ind_perfect_secrecy Enc Gen → perfect_indistinguishability Enc Gen := by
  intro h_ips m1 m2 A
  -- Point-wise equality for all c implies the PMFs themselves are equal.
  have h_eq : Enc_dist Enc Gen m1 = Enc_dist Enc Gen m2 := by
    apply PMF.ext
    intro c
    apply h_ips m1 m2 c
  -- If the input distributions are equal, their bind with any A is also equal.
  rw [h_eq]

/--
Backward direction: Indistinguishability against any probabilistic
adversary implies point-wise indistinguishability.
We construct a specific adversary that outputs 'true' only for a target ciphertext.
-/
theorem perfect_indistinguishability_imp_ind_perfect_secrecy
    [DecidableEq C] (Enc : K → M → C) (Gen : PMF K) :
    perfect_indistinguishability Enc Gen → ind_perfect_secrecy Enc Gen := by
  intro h_pi m1 m2 c
  -- Define a probabilistic adversary A that outputs 'true' with probability 1
  -- if the ciphertext is exactly 'c', and 'false' otherwise.
  let A : C → PMF Bool := fun c' =>
    if c' = c then PMF.pure true else PMF.pure false

  -- From the hypothesis, the resulting output distributions must be identical.
  have h_bind_eq := h_pi m1 m2 A

  -- We evaluate the probability of the output being 'true'.
  -- (Enc_dist m).bind A true should equal (Enc_dist m) c.
  have h_prob (m : M) : ((Enc_dist Enc Gen m).bind A) true = (Enc_dist Enc Gen m) c := by
    rw [PMF.bind_apply]
    simp only [A]
    simp only [apply_ite (fun p : PMF Bool => p true)]
    simp only [PMF.pure_apply, ite_true]
    simp only [Bool.true_eq_false, ↓reduceIte, mul_ite, mul_one, mul_zero, tsum_ite_eq]

  -- Substitute the evaluations back into the equality of distributions.
  rw [← h_prob m1, ← h_prob m2]
  -- Use PMF.ext_iff or congr_fun to get the point-wise equality from the PMF equality.
  exact congr_fun (congr_arg (fun p => p.val) h_bind_eq) true

/--
Main Theorem: Equivalence between point-wise indistinguishability and
adversary-based perfect indistinguishability.
-/
theorem ind_perfect_secrecy_iff_perfect_indistinguishability
    [DecidableEq C] (Enc : K → M → C) (Gen : PMF K) :
    ind_perfect_secrecy Enc Gen ↔ perfect_indistinguishability Enc Gen :=
  ⟨ind_perfect_secrecy_imp_perfect_indistinguishability Enc Gen,
   perfect_indistinguishability_imp_ind_perfect_secrecy Enc Gen⟩


end PerfectSecrecy.Equivalences
