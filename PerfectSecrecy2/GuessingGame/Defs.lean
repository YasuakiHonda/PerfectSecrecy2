import PerfectSecrecy2.Defs
import PerfectSecrecy2.Defs_bit
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform

namespace PerfectSecrecy.GuessingGame

open PMF

variable {K M C : Type} [Fintype K] [Fintype M]
variable [DecidableEq M] [DecidableEq C]

/--
`S Enc c` is the set of all messages `m` such that there exists a key `k`
with `Enc k m = c`. In other words, it is the set of plaintexts reachable
from ciphertext `c` under some key.
-/
def S (Enc : K → M → C) (c : C) : Finset M :=
  Finset.univ.filter (fun m => ∃ k, Enc k m = c)

/-- The advantage quantity `e`: the probability that `m1` is NOT reachable from
    a ciphertext produced by encrypting `m0`, i.e., `Pr[c ← Enc_K(m0); m1 ∉ S Enc c]`. -/
noncomputable
def e (Enc : K → M → C) (Gen : PMF K) (m0 m1 : M) : ENNReal :=
  (do
    let c ← Enc_dist Enc Gen m0
    PMF.pure (if m1 ∉ S Enc c then (1 : ENNReal) else 0)) 1

/-- `e` is at most 1, since it is a probability value. -/
lemma e_le_one (Enc : K → M → C) (Gen : PMF K) (m0 m1 : M) :
    e Enc Gen m0 m1 ≤ 1 := by
  exact PMF.coe_le_one _ _

/-- `e` is finite (not ⊤), since it is a probability value. -/
lemma e_not_top (Enc : K → M → C) (Gen : PMF K) (m0 m1 : M) :
    e Enc Gen m0 m1 ≠ ⊤ := by
  exact PMF.apply_ne_top _ _


/--
The proposed adversary from the textbook proof.
Given a ciphertext `c` and challenge messages `m0`, `m1`:
- If `m1 ∈ S Enc c` (m1 is reachable from c), guess uniformly at random.
- If `m1 ∉ S Enc c` (m1 is unreachable from c), always guess `0` (i.e., m0).
-/
noncomputable
def proposedAdversary (Enc : K → M → C) (_m0 m1 : M) (c : C) : PMF Bit :=
  do
    if m1 ∈ S Enc c then
      let b ← randomBit
      PMF.pure b
    else
      PMF.pure 0

/--
The guessing game experiment (IND-CPA style).
A bit `b` is chosen uniformly; the adversary sees an encryption of `m_b`
and tries to guess `b`.
-/
noncomputable
def guessingGame (Enc : K → M → C) (Gen : PMF K) (m0 m1 : M)
                 (A : C → PMF Bit) : PMF Bool := do
  let b ← randomBit
  let c ← Enc_dist Enc Gen (if b=0 then m0 else m1)
  let b' ← A c
  PMF.pure (b' == b)

end PerfectSecrecy.GuessingGame
