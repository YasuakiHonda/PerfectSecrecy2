/-
Copyright (c) 2025 Yasuaki Honda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yasuaki Honda
-/
import PerfectSecrecy2.Defs

namespace PerfectSecrecy.Equivalences

open PMF

variable {M K C : Type}

open Classical in

/--
Theorem: perfect_indistinguishability (probabilistic, Bool-based) implies
perfect_simulatability (probabilistic, V-based).
-/
theorem perfect_indistinguishability_imp_perfect_simulatability [Inhabited M]
    (Enc : K → M → C) (Gen : PMF K) :
    perfect_indistinguishability Enc Gen → perfect_simulatability Enc Gen := by
  intro h_ind V A
  -- 1. Construct the simulator S using the adversary's behavior on the default message.
  let S : PMF V := (Enc_dist Enc Gen default).bind A
  use S
  intro Msg

  simp only [cipher_dist]
  change (Msg.bind (Enc_dist Enc Gen)).bind A = S
  rw [PMF.bind_bind]

  have h_const : ∀ m, (Enc_dist Enc Gen m).bind A = S := by
    intro m
    apply PMF.ext
    intro v
    open Classical in
    -- A' is the probabilistic adversary for the reduction
    let A' : C → PMF Bit := fun c =>
      (A c).bind (fun v' => if v' = v then PMF.pure 1 else PMF.pure 0)

    have h := h_ind m default A'
    -- congr 2

    have h_prob (m' : M) : ((Enc_dist Enc Gen m').bind A') 1 =
        ((Enc_dist Enc Gen m').bind A) v := by
      rw [PMF.bind_apply, PMF.bind_apply]
      congr with a
      rw [PMF.bind_apply]
      simp only [apply_ite (fun p : PMF Bit => p 1)]
      simp only [PMF.pure_apply, PMF.pure_apply];
      simp only [↓reduceIte, Fin.isValue, one_ne_zero, mul_ite, mul_one, mul_zero, tsum_ite_eq]

    rw [← h_prob m, ← h_prob default]
    -- Extract the probability of 1 from the PMF equality
    exact h

  -- Step 4: Substitute and finalize the sum over Msg
  simp_rw [h_const]
  -- Final Goal: Msg.bind (fun m => S) = S
  apply PMF.ext
  intro v
  rw [PMF.bind_apply]
  rw [@ENNReal.tsum_mul_right]
  simp only [tsum_coe, one_mul]


/--
Theorem: perfect_simulatability (V-based) implies perfect_indistinguishability (Bool-based).
-/
theorem perfect_simulatability_imp_perfect_indistinguishability
    (Enc : K → M → C) (Gen : PMF K) :
    perfect_simulatability Enc Gen → perfect_indistinguishability Enc Gen := by
  intro h_sim m1 m2 A
  -- Instantiate simulatability with V = Bool.
  rcases h_sim Bit A with ⟨S, h_S⟩
  have h1 := h_S (PMF.pure m1)
  have h2 := h_S (PMF.pure m2)
  simp only [cipher_dist, Bind.bind, PMF.pure_bind] at h1 h2 ⊢
  rw [h1, h2]

/--
Main Equivalence Theorem:
Indistinguishability is equivalent to Simulatability.
-/
theorem perfect_indistinguishability_iff_perfect_simulatability [Inhabited M]
    (Enc : K → M → C) (Gen : PMF K) :
    perfect_indistinguishability Enc Gen ↔ perfect_simulatability Enc Gen :=
  ⟨perfect_indistinguishability_imp_perfect_simulatability Enc Gen,
   perfect_simulatability_imp_perfect_indistinguishability Enc Gen⟩

end PerfectSecrecy.Equivalences
