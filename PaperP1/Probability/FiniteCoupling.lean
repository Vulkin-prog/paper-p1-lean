module

public import PaperP1.Probability.L1Norm

/-! # Finite coupling bounds with the probability convention for total variation

The distance is half the ordinary sum of absolute singleton mass differences.
The observations can be dependent and are evaluated on the same sample.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Probability

open PaperP1.Algebra Finset

variable {Ω ι : Type*} [Fintype Ω]

theorem finiteExpectation_mono (P : FiniteProbability Ω) {X Y : Ω → ℝ}
    (h : ∀ ω, X ω ≤ Y ω) : finiteExpectation P.weight X ≤ finiteExpectation P.weight Y := by
  apply sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (h ω) (P.weight_nonneg ω)

theorem finiteExpectation_nonneg (P : FiniteProbability Ω) {X : Ω → ℝ}
    (h : ∀ ω, 0 ≤ X ω) : 0 ≤ finiteExpectation P.weight X :=
  sum_nonneg fun ω _ ↦ mul_nonneg (P.weight_nonneg ω) (h ω)

theorem abs_finiteExpectation_le (P : FiniteProbability Ω) (X : Ω → ℝ) :
    |finiteExpectation P.weight X| ≤ finiteExpectation P.weight (fun ω ↦ |X ω|) := by
  calc
    _ ≤ ∑ ω, |P.weight ω * X ω| := abs_sum_le_sum_abs _ _
    _ = _ := by simp only [finiteExpectation, abs_mul, abs_of_nonneg (P.weight_nonneg _)]

def observationLaw (P : FiniteProbability Ω) (Z : Ω → ℕ) : SignedLaw ℝ :=
  ∑ ω, AddMonoidAlgebra.single (Z ω) (P.weight ω)

def lawTotalVariation (μ ν : SignedLaw ℝ) : ℝ := l1Norm (μ - ν) / 2

def disagreementProbability (P : FiniteProbability Ω) (Z W : Ω → ℕ) : ℝ := by
  classical
  exact finiteExpectation P.weight (fun ω ↦ if Z ω ≠ W ω then 1 else 0)

theorem lawTotalVariation_nonneg (μ ν : SignedLaw ℝ) : 0 ≤ lawTotalVariation μ ν :=
  div_nonneg (l1Norm_nonneg _) (by norm_num)

theorem lawTotalVariation_coupling (P : FiniteProbability Ω) (Z W : Ω → ℕ) :
    lawTotalVariation (observationLaw P Z) (observationLaw P W) ≤
      disagreementProbability P Z W := by
  classical
  unfold lawTotalVariation observationLaw disagreementProbability
  rw [← sum_sub_distrib]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  calc
    _ ≤ ∑ ω, l1Norm (AddMonoidAlgebra.single (Z ω) (P.weight ω) -
        AddMonoidAlgebra.single (W ω) (P.weight ω)) := l1Norm_sum _ _
    _ ≤ ∑ ω, 2 * P.weight ω * (if Z ω ≠ W ω then 1 else 0) := by
      apply sum_le_sum
      intro ω _
      by_cases h : Z ω = W ω
      · simp [h]
      · simp only [h, ne_eq, not_false_eq_true, ↓reduceIte, mul_one]
        have hb := l1Norm_sub (AddMonoidAlgebra.single (Z ω) (P.weight ω))
          (AddMonoidAlgebra.single (W ω) (P.weight ω))
        rw [l1Norm_single, l1Norm_single, abs_of_nonneg (P.weight_nonneg ω)] at hb
        simpa only [two_mul] using hb
    _ = _ := by
      unfold finiteExpectation
      rw [sum_mul]
      apply sum_congr rfl
      intro ω _
      ac_rfl

theorem countLaw_eq_observationLaw (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) : countLaw G P.weight J = observationLaw P (indicatorCount G J) := by
  simp only [countLaw, scalar_mul_atom, observationLaw]

omit [Fintype Ω] in
theorem indicatorCount_sdiff_add [DecidableEq ι] {G H : Finset ι} (hHG : H ⊆ G)
    (J : ι → Ω → Bool) (ω : Ω) :
    indicatorCount (G \ H) J ω + indicatorCount H J ω = indicatorCount G J ω := by
  unfold indicatorCount
  exact sum_sdiff hHG

omit [Fintype Ω] in
theorem indicatorCount_mono {G H : Finset ι} (hHG : H ⊆ G)
    (J : ι → Ω → Bool) (ω : Ω) : indicatorCount H J ω ≤ indicatorCount G J ω :=
  sum_le_sum_of_subset hHG

theorem mean_indicatorCount (P : FiniteProbability Ω) (G : Finset ι)
    (J : ι → Ω → Bool) :
    finiteExpectation P.weight (fun ω ↦ (indicatorCount G J ω : ℝ)) =
      ∑ x ∈ G, exactMarginal P J x := by
  have hind (b : Bool) : (b.toNat : ℝ) = indicatorValue b := by cases b <;> simp [indicatorValue]
  simp only [indicatorCount, Nat.cast_sum, hind, finiteExpectation_sum, exactMarginal]

theorem disagreement_count_subset_le [DecidableEq ι]
    (P : FiniteProbability Ω) {G H : Finset ι} (hHG : H ⊆ G) (J : ι → Ω → Bool) :
    disagreementProbability P (indicatorCount G J) (indicatorCount H J) ≤
      ∑ x ∈ G \ H, exactMarginal P J x := by
  classical
  rw [← mean_indicatorCount]
  apply finiteExpectation_mono
  intro ω
  have hsum := indicatorCount_sdiff_add hHG J ω
  by_cases h : indicatorCount G J ω = indicatorCount H J ω
  · simp only [h, ne_eq, not_true_eq_false, ↓reduceIte]
    exact Nat.cast_nonneg _
  · simp only [h, ne_eq, not_false_eq_true, ↓reduceIte]
    have hpos : 1 ≤ indicatorCount (G \ H) J ω := by omega
    exact_mod_cast hpos

theorem countLaw_subset_coupling [DecidableEq ι]
    (P : FiniteProbability Ω) {G H : Finset ι} (hHG : H ⊆ G) (J : ι → Ω → Bool) :
    lawTotalVariation (countLaw G P.weight J) (countLaw H P.weight J) ≤
      ∑ x ∈ G \ H, exactMarginal P J x := by
  rw [countLaw_eq_observationLaw, countLaw_eq_observationLaw]
  exact (lawTotalVariation_coupling _ _ _).trans (disagreement_count_subset_le P hHG J)

end PaperP1.Probability
