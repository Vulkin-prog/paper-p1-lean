module

public import PaperP1.Model.OldSpaceProjection
public import PaperP1.Model.FiniteSplitLp

/-! # Actual old-space projected split-product tuples and their Holder bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectedSplitTuples

open scoped ENNReal
open Finset MeasureTheory PaperP1.Arithmetic PaperP1.Model PaperP1.Affine
open PaperP1.OldSpaceProjection PaperP1.SplitOffsetProducts PaperP1.FiniteSplitLp
open PaperP1.Model.InfiniteRademacher

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tuples (O : Finset ℕ) (A : ι → Finset ℤ) (S : ι → Finset ℕ) : Finset (∀ i, S i) := by
  classical
  exact univ.filter fun n ↦ (∑ i, parityVec (product (A i) (n i).val)) ∈ oldSpace O

def cutoff (O : Finset ℕ) (A : ι → Finset ℤ) (S : ι → Finset ℕ) : ℕ :=
  max (O.sup id) ((univ : Finset ι).sup fun i ↦ (S i).sup (fun n ↦ product (A i) n))

omit [DecidableEq ι] in
theorem cutoff_old (O : Finset ℕ) (A : ι → Finset ℤ) (S : ι → Finset ℕ) (n : ℕ) (hn : n ∈ O) :
    n ≤ cutoff O A S := by
  have h : n ≤ O.sup id := le_sup (f := id) hn
  unfold cutoff
  exact h.trans (le_max_left _ _)

omit [DecidableEq ι] in
theorem cutoff_value (O : Finset ℕ) (A : ι → Finset ℤ) (S : ι → Finset ℕ)
    (i : ι) (n : ℕ) (hn : n ∈ S i) : product (A i) n ≤ cutoff O A S := by
  have h₁ : product (A i) n ≤ (S i).sup (fun n ↦ product (A i) n) := le_sup hn
  have h₂ : (S i).sup (fun n ↦ product (A i) n) ≤
      (univ : Finset ι).sup (fun j ↦ (S j).sup (fun n ↦ product (A j) n)) := le_sup (f := fun j : ι ↦ (S j).sup (fun n ↦ product (A j) n)) (mem_univ i)
  unfold cutoff
  exact h₁.trans (h₂.trans (le_max_right _ _))

theorem fixed_motif_holder (O : Finset ℕ) (A : ι → Finset ℤ) (S : ι → Finset ℕ)
    (a : ℝ) (ha : 0 < a) (v : ℕ) (hv : 0 < v) (hav : 1 / a + Fintype.card ι / (v : ℝ) = 1) :
    ((tuples O A S).card : ℝ) ≤ ((2 : ℝ) ^ O.card) ^ (Fintype.card ι / (v : ℝ)) *
      ∏ i, lpNorm (PaperP1.ShortSplitMoments.sumValue (A i) (S i)) (v : ℝ≥0∞) infiniteRademacherMeasure := by
  classical
  let M := cutoff O A S
  let L : ∀ i, S i → SampleSpace M →ₗ[F₂] F₂ := fun i n ↦ valueLinear M (product (A i) n.val)
  have htuples : PaperP1.ProjectedCharacterTuples.tuples (characterSpace M O) L = tuples O A S := by
    ext n
    simp only [PaperP1.ProjectedCharacterTuples.tuples, tuples, mem_filter, mem_univ, true_and]
    exact sum_valueLinear_mem_iff M O (cutoff_old O A S) (fun i ↦ product (A i) (n i).val)
      (fun i ↦ cutoff_value O A S i (n i).val (n i).property)
  have hp := PaperP1.ProjectionHolder.projected_count_holder (characterSpace M O) L a v ha
    (by exact_mod_cast hv) hav
  rw [htuples] at hp
  have hroot : ∀ i, (PaperP1.Algebra.finiteExpectation (cylinderProbability M).weight
      (fun σ ↦ |PaperP1.ProjectedCharacterTuples.sumValue L i σ| ^ (v : ℝ))) ^ (1 / (v : ℝ)) =
      lpNorm (PaperP1.ShortSplitMoments.sumValue (A i) (S i)) (v : ℝ≥0∞) infiniteRademacherMeasure := by
    intro i
    have hsum : PaperP1.ProjectedCharacterTuples.sumValue L i = finiteSum M (A i) (S i) := by
      funext σ
      change (∑ n : S i, (randomMultiplicativeValue σ (product (A i) n.val) : ℝ)) = _
      exact sum_coe_sort (S i) (fun n ↦ (randomMultiplicativeValue σ (product (A i) n) : ℝ))
    rw [hsum]
    exact moment_root_eq_lpNorm M (A i) (S i) (cutoff_value O A S i) v hv
  have hr : 1 - 1 / a = Fintype.card ι / (v : ℝ) := by linarith
  change ((tuples O A S).card : ℝ) ≤ (Fintype.card (characterSpace M O) : ℝ) ^ (1 - 1 / a) *
    ∏ i, (PaperP1.Algebra.finiteExpectation (cylinderProbability M).weight
      (fun σ ↦ |PaperP1.ProjectedCharacterTuples.sumValue L i σ| ^ (v : ℝ))) ^ (1 / (v : ℝ)) at hp
  simp only [hroot, hr] at hp
  have hcard : (Fintype.card (characterSpace M O) : ℝ) ≤ (2 : ℝ) ^ O.card := by
    exact_mod_cast characterSpace_card_le M O
  exact hp.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (by positivity) hcard (by positivity)) (prod_nonneg fun _ _ ↦ lpNorm_nonneg))

end PaperP1.ProjectedSplitTuples
