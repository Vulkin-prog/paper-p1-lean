module

public import PaperP1.Model.AllPairOriginalLaws

/-! # Mean bounds for the genuine original filtered count laws -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllPairCountMeans

open Finset MeasureTheory PaperP1.Algebra PaperP1.Probability PaperP1.Model
  PaperP1.Model.InfiniteStarts PaperP1.PositionalFiniteLaw PaperP1.PositionalPairDeletion
  PaperP1.PositionalCountProjection PaperP1.AllPairOriginalLaws

def goodMean (H : ℝ) (N L : ℕ) : ℝ := ∫ k, (k : ℝ) ∂(goodLaw H N L : Measure ℕ)

def allMean (N L : ℕ) : ℝ := ∫ k, (k : ℝ) ∂(allLaw N L : Measure ℕ)

theorem goodMean_nonneg (H : ℝ) (N L : ℕ) : 0 ≤ goodMean H N L :=
  integral_nonneg (fun _ ↦ Nat.cast_nonneg _)

theorem allMean_nonneg (N L : ℕ) : 0 ≤ allMean N L :=
  integral_nonneg (fun _ ↦ Nat.cast_nonneg _)

theorem goodMean_le_original (H : ℝ) (N L : ℕ) :
    goodMean H N L ≤ CountObservables.countMoment (dyadicBlock N) L 1 := by
  let S := dyadicBlock N
  let M := PositionalObservationLaw.cutoff S L
  let P := cylinderProbability M
  let J := fun x ↦ startIndicator (M := M) x L
  have hcut (x : ℕ) (hx : x ∈ S) : x + L ≤ M := le_sup (f := fun x ↦ x + L) hx
  have he : goodMean H N L = finiteExpectation P.weight
      (fun ω ↦ (totalCount (isolate (GoodEdgeCompression.goodEdges H N L) (configuration S J ω)) : ℝ)) :=
    FiniteObservationLaw.integral_eq _ _ _
  rw [he]
  calc
    _ ≤ finiteExpectation P.weight (fun ω ↦ (totalCount (configuration S J ω) : ℝ)) :=
      finiteExpectation_mono P (fun ω ↦ by exact_mod_cast totalCount_isolate_le _ (configuration S J ω))
    _ = ∑ x ∈ S, exactMarginal P J x := by
      simp only [totalCount_configuration]
      exact mean_indicatorCount P S J
    _ = ∑ x ∈ S, infiniteMarginal x L := sum_congr rfl
      (fun x hx ↦ (infiniteMarginal_eq_finite (hcut x hx)).symm)
    _ = _ := (CountObservables.countMoment_one (Subset.rfl : S ⊆ dyadicBlock N)).symm

theorem allMean_le_good {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (H : ℝ) :
    allMean N L ≤ goodMean H N L := by
  have hh := (original_cost hN hL H).2.1
  exact sub_nonneg.mp hh

end PaperP1.AllPairCountMeans
