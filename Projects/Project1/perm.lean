import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Real.Basic

open MeasureTheory ProbabilityTheory ENNReal BigOperators
set_option maxHeartbeats 0

-- 1. Define the Sample Space (Ω)
variable {n : ℕ}

-- abbrev Ω := Equiv.Perm (Fin n)

-- Apparently one cannot use the abbreviation, but we use a local notation
local notation "Ω" => Equiv.Perm (Fin n)

-- 2. Define the Measurable Space
instance : MeasurableSpace Ω := ⊤
instance : MeasurableSingletonClass Ω := ⟨by simp⟩

-- 3. Define the Probability Measure (P) manually (this is just a uniform over all permutations)
-- TODO: probably we can use PMF.uniformOfFinset...
-- We define a function that assigns 1/n! to every outcome.
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

-- We need this to prove that isAncestor integral will be Integrable
noncomputable instance (n : ℕ) : IsProbabilityMeasure (P (n := n)) :=
  PMF.toMeasure.isProbabilityMeasure permPMF
noncomputable instance (n : ℕ) : IsFiniteMeasure (P (n := n)) := by
  infer_instance

-- 4. Define the Random Variable isAncestor
-- Actually, isAncestor will be a function of j, k that returns a random variable
-- The result is 1 if perm(j) > perm([j, k]), else 0
noncomputable def isAncestor (j k : Fin n) : Ω → ℝ :=
  fun perm =>
    if ∀ i ∈ Finset.Icc (min j k) (max j k), i ≠ j → perm j > perm i then 1 else 0
  #check isAncestor

-- 6. Calculate the expected value of being an ancestor
theorem prob_is_ancestor_j_le_k (j k : Fin n) (j_le_k : j ≤ k) :
    ∫ ω, isAncestor j k ω ∂P = 1 / (Finset.Icc (min j k) (max j k)).card := by
    classical

    -- 1. Rewrite into a sum
    simp only [P, PMF.integral_eq_sum, smul_eq_mul]

    -- 2. Simplify the sum
    simp only [permPMF, PMF.ofFintype_apply, perm_prob, one_div, toReal_inv, toReal_natCast]

    -- 3. Take out the constant factor (and move it to the RHS)
    simp only [← Finset.mul_sum]
    field_simp

    -- 4. Unfold isAncestor and convert to a cardinality problem
    simp only [isAncestor]
    -- Do not simplify too much!
    -- (no) simp only [Finset.mem_Icc]

    rw [Finset.sum_boole]

    rw [← Finset.natCast_card_mul_nnratCast_dens]
    field_simp

    -- 5. Simplify the expressions, try to obtain A.card * B.card = Fintype.card Ω
    simp only [Finset.dens, gt_iff_lt, NNRat.cast_div,
      NNRat.cast_natCast, one_div]

    have denom_neq_0 : ↑(Finset.Icc (min j k) (max j k)).card ≠ 0 := by
      simp only [Fin.card_Icc, Fin.coe_max, Fin.coe_min]
      omega

    field_simp

    -- 6. Convert to Nat cardinals
    norm_cast -- Cast everything to Nat https://proofassistants.stackexchange.com/questions/4113/how-to-perform-type-conversion-coercion-in-lean-4

    -- 7. Prove by cases, j < k and j > k
    rw [min_eq_left (by omega), max_eq_right (by omega)]
    -- Call the interval S
    set S : Finset (Fin n) := Finset.Icc j k

    -- 8. Define A t where t is the index of the maximum in S.
    -- A is the set of permutations where this is true
    let A (t : Fin n) : Finset Ω :=
      {x : Ω | ∀ i ∈ S, ¬i = t → x i < x t}
      -- Finset.filter (fun x => ∀ i ∈ S, ¬i = t → x i < x t) (Ω.finsetEquivSet)

    -- We'll show that the sets A t for t ∈ S partition Ω
    -- then that each A t has the same cardinality, since we have trivially |S| such sets,
    -- we'll be able to calculate the cardinality of A t as |Ω| / |S|

    -- Union over t ∈ S of A t is Ω
    -- biUnion takes each element of S and maps A to it
    -- Also here, it's equal to the universe of the set given by Ω
    -- (Finset.univ is magical and autoguesses stuff)
    have part_union : Finset.biUnion S A = (Finset.univ : Finset Ω) := by
      simp [A]

      by_cases hc : n = 0
      · subst hc
        simp [Equiv.Perm]
        grind
      -- n > 0 from here

      ext

      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      rename_i perm

      -- We need to choose the maximum perm element to be a
      have s_map_nonempty : Finset.Nonempty (S.image (fun x => perm x)) := by
        simp [S]
        exact j_le_k

      -- Get the maximum element
      let m := Finset.max' (S.image (fun x => perm x)) s_map_nonempty
      have hm : m ∈ S.image (fun x : Fin n => perm x) := by
        subst m
        exact Finset.max'_mem (Finset.image (fun x ↦ perm x) S) s_map_nonempty

      -- Extract the corresponding index
      have exists_t := Finset.mem_image.mp hm
      obtain ⟨t, t_in_s, perm_t_eq_m⟩ := exists_t

      -- Use this index
      use t

      constructor
      · -- Prove t ∈ S
        exact t_in_s
      · -- Prove perm t is maximum
        intro i hi i_neq_t
        simp_all [m, S]
        -- have : perm i ∈ (Finset.image (fun x ↦ perm x) S) := by sorry
        refine
          Finset.lt_max'_of_mem_erase_max' (Finset.image (fun x ↦ perm x) S)
            s_map_nonempty ?_

        -- Prove that perm i is in the set without the maximum
        simp_all

        rw [← perm_t_eq_m]
        constructor
        · simpa using i_neq_t
        · -- Prove i ∈ S
          simpa [S] using hi -- Trying this new tactic lol

    -- Intersection between any two instances of A is empty
    have part_inter : Set.PairwiseDisjoint S A := by
      simp_all [Set.PairwiseDisjoint, Set.Pairwise, Disjoint]
      intro x hx y yx neq perm perm_x perm_y
      grind

    -- Rewrite the univ set cardinality
    have partition_card : (Finset.biUnion S A).card = Fintype.card Ω := by
      rw [part_union]
      rfl

    rw [← partition_card]
    rw [Finset.card_biUnion part_inter]

    -- Prove that for every i, j in S, (A i).card = (A j).card
    have A_sum_i_j_eq : ∀ i ∈ S, ∀ j ∈ S, (A j).card = (A i).card := by
      intro i hi j hj

      -- Define a equivalence that maps a permutation to the same with i, j swapped
      let e : Ω ≃ Ω :=
      { toFun     := fun x => (Equiv.swap i j).trans x
        invFun    := fun x => (Equiv.swap i j).trans x
        left_inv  := by intro x; ext t; simp
        right_inv := by intro x; ext t; simp }

      -- Show that applying the equivalence to (A i) creates (A j)
      have himage : A j = Finset.image e (A i) := by
        simp [e]
        ext x
        constructor
        · intro hx
          simp_all
          use (Equiv.swap i j).trans x -- Undo the transformation
          grind
        · intro hx
          simp_all
          obtain ⟨perm, ⟨perm_in_ai, e_perm_eq_x⟩⟩ := hx
          grind

      -- Show that carinality of (A i) is the same as its image with e by injectivity
      have : (A i).card = (Finset.image e (A i)).card := by
          symm
          exact Finset.card_image_of_injective (A i) e.injective

      rw [this]
      rw [himage]

    -- Use this to prove the size of each A t is the same (and in this case A j)
    have A_size_eq : ∀ u ∈ S, (A u).card = (A j).card := by
      exact A_sum_i_j_eq j (by simpa [S])

    -- Prove that sum over u is the same as applying it to j
    have A_sum_const : ∑ u ∈ S, (A u).card = ∑ u ∈ S, (A j).card := by
      apply Finset.sum_congr (by rfl)
      exact A_size_eq

    rw [A_sum_const]

    -- Rewrite the sum of a constant value
    rw [Finset.sum_const, smul_eq_mul]

    -- Apply commutative property
    rw [Nat.mul_comm]

theorem prob_is_ancestor (j k : Fin n) :
    ∫ ω, isAncestor j k ω ∂P = 1 / (Finset.Icc (min j k) (max j k)).card := by
    by_cases hjk : j < k
    · exact prob_is_ancestor_j_le_k j k (by omega)
    · sorry

-- 5. Define a new class of random variables depth, which is the sum of all ancestors
noncomputable def depth (k : Fin n) : Ω → ℝ :=
  ∑ j : Fin n, isAncestor j k

#check depth

theorem expected_depth (k : Fin n) :
    ∫ ω, depth k ω ∂P ≤ 1 + 2 * Real.log n := by

    -- Create a sum of isAncestor integrals
    unfold depth

    -- Map the functions to allow simplification
    have h_eval :
      (fun ω => (∑ i : Fin n, isAncestor i k) ω)
        = (fun ω => ∑ i : Fin n, isAncestor i k ω) := by
      simp only [Finset.sum_apply]

    -- Now rewrite the integral using that
    rw [h_eval]
    clear h_eval
    rw [MeasureTheory.integral_finset_sum]

    -- Map the functions to substitute the integral
    have h_eval :
      (fun i => ∫ (a : Ω), isAncestor i k a ∂P)
        = (fun i => (1 / (Finset.Icc (min i k) (max i k)).card : ℝ)) := by
      simp only [prob_is_ancestor]

    -- Plug the sum
    rw [h_eval]
    clear h_eval

    -- Prove n = 0 case here to allow simplifying the logarithms later
    by_cases hc : n = 0
    · subst hc
      simp
    rw [← ne_eq, Nat.ne_zero_iff_zero_lt] at hc

    -- Abbrev as f, L, R
    set f : Fin n → ℝ := fun i => 1 / (Finset.Icc (min i k) (max i k)).card
    set L : Finset (Fin n) := Finset.Iio k
    set R : Finset (Fin n) := Finset.Ioi k

    have : Finset.univ.sum f = ∑ i, f i := by rfl
    rw [this]; clear this

    have split_sum : ∑ i, f i = ∑ i ∈ L, f i + f k + ∑ i ∈ R, f i := by
      have : Finset.univ = L ∪ {k} ∪ R := by
        simp [L, R, ← Finset.filter_ge_eq_Iic, ← Finset.filter_lt_eq_Ioi]
        grind
      rw [this]; clear this
      repeat rw [Finset.sum_union]
      · simp
      · simp [L]
      · simp [L, R, ← Finset.filter_gt_eq_Iio, ← Finset.filter_lt_eq_Ioi, Disjoint]
        grind

      -- alt proof (maybe with a bit less automation)
      -- simp [← Finset.sum_compl_add_sum L]
      -- rw [add_comm]
      -- have : Lᶜ = {j} ∪ R := by
      --   simp [L, R, ← Finset.filter_gt_eq_Iio, ← Finset.filter_le_eq_Ici]
      -- rw [this]; clear this
      -- rw [Finset.sum_union ?_]
      -- simp
      -- grind
      -- simp [R]

    -- Finally split the sum
    rw [split_sum]; clear split_sum

    -- Now calculate each part of the sum
    have k_sum : f k = 1 := by
      simp [f]

    -- TODO: there's a bit of mess with casts here
    -- also we forced iccs from 1 to use harmonic bounds
    -- TODO: differs by the pdf proof because it's 0-indexed (to use Fin n)
    have ik_sum : ∑ i ∈ L, f i = ∑ i ∈ Finset.Icc 1 (k + 1 : ℕ), (i : ℚ)⁻¹ - 1 := by
      simp_all [f, L]

      -- #check Finset.map
      -- #check Finset.sum_bij
      -- #check Finset.sum_comp

      -- rw [← Finset.filter_gt_eq_Iio]
      -- -- rw [max_eq_right ?_]
      -- -- have : (fun (x : Fin n) => ((max x k + 1 - min x k) : ℝ)⁻¹) =
      -- --         (fun (x : Fin n) => (k + 1 - x : ℝ)⁻¹) := by simp
      -- -- sorry
      -- simp

      sorry

    have ki_sum : ∑ i ∈ R, f i = ∑ i ∈ Finset.Icc 1 (n - k : ℕ), (i : ℚ)⁻¹ - 1 := by
      sorry

    -- Rewrite it in the goal
    rw [k_sum, ik_sum, ki_sum]
    rw [← harmonic_eq_sum_Icc (n := k + 1)]
    rw [← harmonic_eq_sum_Icc (n := n - k)]

    -- Use bounds on logs (<3 Arend Mellendijk)
    grw [harmonic_le_one_add_log (n := k + 1)]
    grw [harmonic_le_one_add_log (n := n - k)]


    -- Rewrite log k < log n since k < n (and the same for n - k + 1)
    -- TODO: fix all format + names with lt + casts
    have log_k_lt_logn : Real.log (k + 1 : ℝ) ≤ Real.log (n : ℝ) := by
      rw [Real.log_le_log_iff] <;> norm_cast
      · simp [Nat.add_one_le_iff]
      · simp

    have log_n_k_1_lt_logn : Real.log (n - k : ℝ) ≤ Real.log (n : ℝ) := by
      rw [Real.log_le_log_iff] <;> norm_cast
      · rw [Int.subNatNat_of_le (by simp)]
        simp
      · rw [Int.subNatNat_of_le (by simp)]
        simp

    simp only [add_sub_cancel_left, Nat.cast_add, Fin.is_le', Nat.cast_sub, Nat.cast_one, ge_iff_le]
    grw [log_k_lt_logn]
    grw [log_n_k_1_lt_logn]

    -- Rearrange terms
    calc
      Real.log ↑n + 1 + Real.log ↑n = 1 + Real.log ↑n + Real.log ↑n := by rw [add_comm _ 1]
      _ = 1 + (Real.log ↑n + Real.log ↑n) := by rw [add_assoc]
      _ ≤ 1 + 2 * Real.log ↑n := by rw [← two_mul]

    · intro i hi
      unfold isAncestor
      exact MeasureTheory.Integrable.of_finite -- uses the FiniteMeasure instance
