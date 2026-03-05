import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform

/-- Bit is defined as Fin 2 -/
abbrev Bit := Fin 2
theorem Bit_eq_Fin2 : Bit = Fin 2 := by rfl

open BigOperators

/-- The sum of a function over all bits (0 and 1) can be expressed
as the sum of its values at 0 and 1. -/
theorem tsum_bit {f : Bit → ENNReal} : (∑' (b : Bit), f b) = f 0 + f 1 := by
  rw [tsum_fintype]
  rw [Fin.sum_univ_two]

/-- `randomBit` is a PMF that outputs 0 or 1 with equal probability. -/
noncomputable
abbrev randomBit : PMF (Bit) :=
  PMF.uniformOfFintype Bit

/-- The probability that `randomBit` outputs either 0 or 1 is 1/2. -/
theorem randomBit_apply (b : Bit) : randomBit b = 1/2 := by
  rw [randomBit, PMF.uniformOfFintype_apply]
  simp only [one_div, Bit_eq_Fin2, Fintype.card_fin, Nat.cast_two]
