import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Data.Real.Basic

open MeasureTheory ProbabilityTheory ENNReal BigOperators

-- 1. Define the Sample Space (Ω)
inductive Coin
| heads
| tails
deriving Repr, DecidableEq, Fintype, Inhabited

-- Common notation for sample space
abbrev Ω := Coin

-- 2. Define the Measurable Space
-- "discreteMeasurableSpace" means every subset is measurable.
instance : MeasurableSpace Ω := ⊤
instance : MeasurableSingletonClass Ω := ⟨by simp⟩ -- works also without this line

-- 3. Define the Random Variable X
-- X(heads) = 1, X(tails) = 0
def X : Ω → ℝ
| Coin.heads => 1
| Coin.tails => 0

-- 4. Define the Probability Measure (P) manually
-- We define a function that assigns 1/2 to every outcome.
noncomputable def coin_prob (_ : Ω) : ℝ≥0∞ := 1/2

-- We prove that the sum of probabilities is 1.
theorem coin_prob_sum_one : ∑ ω : Ω, coin_prob ω = 1 := by
  -- Expand the sum over the finite set {heads, tails}
  have : (Finset.univ : Finset Ω) = {Coin.heads, Coin.tails} := by
    ext x; cases x <;> simp
  rw [this, Finset.sum_insert, Finset.sum_singleton]
  · simp [coin_prob]
    -- 1/2 + 1/2 = 1 in ENNReal
    ring_nf
    rw [ENNReal.inv_mul_cancel]
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    · simp only [ne_eq, ofNat_ne_top, not_false_eq_true]
  · simp

-- Create the PMF object using the function and the proof
noncomputable def coinPMF : PMF Ω := PMF.ofFintype coin_prob coin_prob_sum_one

-- Convert the PMF to a Measure (P)
noncomputable def P : Measure Ω := coinPMF.toMeasure

-- 5. Prove the Expected Value of X is 0.5
theorem expected_value_coin : ∫ ω, (X ω) ∂P = 1/2 := by
  -- Unfold P to reveal it is based on a PMF
  unfold P coinPMF

  -- 1. Convert the Bochner integral (∫) to an infinite sum (∑')
  rw [PMF.integral_eq_sum]

  -- 2. Substitute the PMF definition
  simp only [PMF.ofFintype_apply, smul_eq_mul, one_div]

  -- We have  `∑ x, (coin_prob x).toReal * X x = 2⁻¹`

  -- 3. Unfold coin_prob definition (just 1/2)
  unfold coin_prob

  -- 4. Convert to a sum over Finset.univ
  rw [← Fintype.sum_ite_mem Finset.univ]

  -- 5. Explicitly expand the finite set {heads, tails}
  -- We prove that the universe of Coin is just these two elements.
  have univ_eq : (Finset.univ : Finset Coin) = {Coin.heads, Coin.tails} := by
    ext x; cases x <;> simp
  rw [univ_eq]

  -- 6. Compute the sum
  simp -- Simplify the sum → `2⁻¹ * X Coin.heads + 2⁻¹ * X Coin.tails = 2⁻¹`
  simp only [X] -- We get `2⁻¹ * 1 + 2⁻¹ * 0 = 2⁻¹`
  norm_num -- Finish the arithmetic
