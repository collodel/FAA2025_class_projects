import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Data.Real.Basic

open MeasureTheory ProbabilityTheory ENNReal BigOperators

-- 1. Define the Sample Space (Ω)
abbrev Ω := Equiv.Perm (Fin 10)

-- 2. Define the Measurable Space
instance : MeasurableSpace Ω := ⊤
instance : MeasurableSingletonClass Ω := ⟨by simp⟩

-- 3. Define the Random Variable X
-- Actually, X will be a function of j,k that returns a random variable
-- The result is 1 if perm(j) > perm(k), else 0
-- TODO: tau?
noncomputable def X (j k : Fin 10) : Ω → ℝ :=
  fun perm =>
    if perm j > perm k then 1 else 0
#check X

-- Alternative syntax
-- def X' (j k : Fin 10) : Ω → ℝ
-- | p => if p j > p k then 1 else 0
-- #check X'


-- 4. Define the Probability Measure (P) manually (this is just a uniform over all permutations)
-- We define a function that assigns 1/10! to every outcome.
noncomputable def perm_prob (_ : Ω) : ℝ≥0∞ := 1 / (Fintype.card Ω)

-- We prove that the sum of probabilities is 1.

-- Do it for a generic uniform probability to avoid calculating 10!
theorem uniform_prob_sum_one {α : Type*} [Fintype α] [Nonempty α] (ω : α → ℝ≥0∞) (h : ∀ a : α, ω a = 1 / (Fintype.card α)) :
    ∑ a : α, ω a = 1 := by
  simp only [h]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_div]
  rw [ENNReal.mul_inv_cancel] -- cancel the terms
  · simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true] -- finish the arithmetic
  · simp only [ne_eq, natCast_ne_top, not_false_eq_true]

theorem perm_prob_sum_one : ∑ ω : Ω, perm_prob ω = 1 := by
  exact uniform_prob_sum_one perm_prob (congrFun rfl)

-- Create the PMF object using the function and the proof
noncomputable def permPMF : PMF Ω := PMF.ofFintype perm_prob perm_prob_sum_one

-- Convert the PMF to a Measure (P)
noncomputable def P : Measure Ω := permPMF.toMeasure

-- 5. Prove the Expected Value of X is 0.5 (when j ≠ k)
theorem expected_value_perm (j k : Fin 10) (h : j ≠ k) (div_sz : 2 ∣ Fintype.card Ω) : ∫ ω, (X j k ω) ∂P = 1/2 := by
  unfold P permPMF

  -- Convert integral to sum
  rw [PMF.integral_eq_sum]

  -- Substitute the PMF definition
  simp only [PMF.ofFintype_apply, smul_eq_mul, one_div]

  -- Prove that P[j < k] is the same of P[k < j]
  simp_all [X]
  -- have symmetry : (∑ x, if x k < x j then (perm_prob x).toReal else 0) =
  --                 (∑ x, if x k > x j then (perm_prob x).toReal else 0) := by sorry
  simp_all [perm_prob]

  -- Remember, i'm counting all x's such that the perm(k) < perm(j)
  have half_set : Fintype.card {x : Ω | x k < x j} = Fintype.card Ω / 2 := by sorry

  -- current goal: (∑ x, if x j < x k then (↑(Fintype.card Ω))⁻¹ else 0) = 2⁻¹
  rw [← Finset.sum_filter]
  simp_all only [Finset.sum_const, nsmul_eq_mul]
  rw [← Set.toFinset_card] at half_set
  rw [← Set.toFinset_setOf]
  rw [half_set]

  field_simp
  rw [Nat.cast_div_charZero ?_]
  · simp
  · exact div_sz


-- theorem expected_value_perm' (j k : Fin 10) (h_neq : j ≠ k) :
--   ∫ ω, X j k ω ∂P = 1/2 := by
--   -- 1. Setup integrals and sums
--   unfold P permPMF
--   rw [PMF.integral_eq_sum]
--   simp only [PMF.ofFintype_apply, perm_prob_val, ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.one_toReal]

--   -- 2. Pull the constant (1 / card Ω) out of the sum
--   -- We use ← Finset.mul_sum to pull the constant factor out
--   rw [← Finset.mul_sum]

--   -- 3. Define the two halves of the sum
--   let S_gt := ∑ x : Ω, if x j > x k then (1 : ℝ) else 0
--   let S_lt := ∑ x : Ω, if x j < x k then (1 : ℝ) else 0

--   -- 4. Prove that S_gt + S_lt = Total Card
--   have sum_parts : S_gt + S_lt = Fintype.card Ω := by
--     -- Combine the sums
--     rw [← Finset.sum_add_distrib]
--     -- Simplify the inside: (if j>k then 1 else 0) + (if j<k then 1 else 0)
--     apply Finset.sum_const_nat
--     intro x _
--     -- Since j ≠ k, exactly one case is true
--     have neq : x j ≠ x k := by exact (Equiv.injective x).ne h_neq
--     by_cases h_gt : x j > x k
--     · simp [h_gt, not_lt_of_gt h_gt] -- if j>k is true, then 1+0 = 1
--     · simp [h_gt] at *               -- if j>k is false...
--       have h_lt : x j < x k := lt_of_le_of_ne (le_of_not_gt h_gt) neq
--       simp [h_lt]                    -- then 0+1 = 1

--   -- 5. KEY STEP: Prove S_gt = S_lt using Symmetry
--   have symmetry : S_gt = S_lt := by
--     unfold S_gt S_lt
--     -- We re-index the sum by multiplying every permutation by (swap j k)
--     -- This is a valid change of variables because it's a bijection.
--     let swap_map := Equiv.mulRight (Equiv.swap j k)
--     rw [Fintype.sum_equiv swap_map]
--     · intro x
--       -- Now we simplify what happens to the condition
--       simp only [Equiv.mulRight_apply, Equiv.Perm.coe_mul, Function.comp_apply]
--       -- (x * swap)(j) becomes x(k)
--       rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
--       -- The condition (x k > x j) is identical to (x j < x k)
--       congr 1
--       simp only [gt_iff_lt]
--     · simp -- Discharges side goal that the equiv maps univ to univ

--   -- 6. Final Arithmetic
--   -- We have `1/N * S_gt = 1/2`
--   -- Substitute S_gt with N/2
--   rw [← symmetry] at sum_parts
--   -- 2 * S_gt = N
--   have h_val : S_gt = (Fintype.card Ω) / 2 := by
--     linarith [sum_parts]

--   -- Substitute back into the main goal
--   -- Note: We use `X` definition to match S_gt
--   have h_goal_match : (∑ x : Ω, X j k x) = S_gt := by
--     apply Finset.sum_congr rfl
--     intro x _
--     simp [X]

--   rw [h_goal_match, h_val]

--   -- Final calculus: (1/N) * (N/2) = 1/2
--   field_simp [Fintype.card_ne_zero]
--   ring



-- -- 5. Prove the Expected Value of X is 0.5
-- theorem expected_value_coin : ∫ ω, (X ω) ∂P = 1/2 := by
--   -- Unfold P to reveal it is based on a PMF
--   unfold P coinPMF

--   -- 1. Convert the Bochner integral (∫) to an infinite sum (∑')
--   rw [PMF.integral_eq_sum]

--   -- 2. Substitute the PMF definition
--   simp only [PMF.ofFintype_apply, smul_eq_mul, one_div]

--   -- We have  `∑ x, (coin_prob x).toReal * X x = 2⁻¹`

--   -- 3. Unfold coin_prob definition (just 1/2)
--   unfold coin_prob

--   -- 4. Convert to a sum over Finset.univ
--   rw [← Fintype.sum_ite_mem Finset.univ]

--   -- 5. Explicitly expand the finite set {heads, tails}
--   -- We prove that the universe of Coin is just these two elements.
--   have univ_eq : (Finset.univ : Finset Coin) = {Coin.heads, Coin.tails} := by
--     ext x; cases x <;> simp
--   rw [univ_eq]

--   -- 6. Compute the sum
--   simp -- Simplify the sum → `2⁻¹ * X Coin.heads + 2⁻¹ * X Coin.tails = 2⁻¹`
--   simp only [X] -- We get `2⁻¹ * 1 + 2⁻¹ * 0 = 2⁻¹`
--   norm_num -- Finish the arithmetic
