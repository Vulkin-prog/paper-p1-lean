module

public import PaperP1.Model.RetainedActiveSubsetMoments

/-! # Companion T22.6: the exact moment decomposition of the actual modified count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedModifiedMomentDecomposition

open Finset MeasureTheory PaperP1.Arithmetic PaperP1.Algebra PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Model.InfiniteRademacher PaperP1.RetainedActiveCount PaperP1.RetainedActiveSubsetMoments
  PaperP1.RegularStarts PaperP1.RetainedReferenceTheorem PaperP1.RetainedCardinalityDeficits

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem pointwise (H : ℝ) (N L r : ℕ) (hr : 1 ≤ r) (ω : InfiniteSample) :
    ((modified H N L (regularStarts N L) ω).choose r : ℝ) =
      (direct L r (activeSet (regularStarts N L) L ω) : ℝ) +
      (pair H N L r (activeSet (regularStarts N L) L ω) : ℝ) -
      (if ¬retainedActive H N L (regularStarts N L) ω then (direct L r (activeSet (regularStarts N L) L ω) : ℝ) else 0) -
      (if ¬retainedActive H N L (regularStarts N L) ω then (pair H N L r (activeSet (regularStarts N L) L ω) : ℝ) else 0) := by
  let A := activeSet (regularStarts N L) L ω
  have hcard := activeSet_card (regularStarts N L) L ω
  by_cases hret : retainedActive H N L (regularStarts N L) ω
  · have h := RetainedSubsetCounts.choose_decomposition (fun x ↦ squareClassSpace x L)
      (GoodEdgeCompression.goodEdges H N L) (RetainedGoodEdges.good_pair_card H N L)
      (fun e he ↦ RetainedGoodEdges.good_pair_positive H N L e he) A
      ((retained_predicate H N L A).mp hret) r
    rw [modified, ite_eq_left hret]
    simp only [hret, not_true_eq_false, ite_false, sub_zero]
    rw [← hcard, direct_eq_subsets]
    exact_mod_cast h
  · rw [modified, ite_eq_right hret]
    simp only [hret, not_false_eq_true, ite_true, Nat.choose_eq_zero_of_lt (by omega : 0 < r), Nat.cast_zero]
    ring

theorem decomposition (H : ℝ) (N L r : ℕ) (hr : 1 ≤ r) :
    modifiedChooseMoment H N L r = directMean N L r + pairMean H N L r - directLeakage H N L r - pairLeakage H N L r := by
  let G := regularStarts N L
  let f := fun A : Finset ℕ ↦ (direct L r A : ℝ)
  let g := fun A : Finset ℕ ↦ (pair H N L r A : ℝ)
  let d := fun A : Finset ℕ ↦ if ¬RetainedGoodEdges.Retained H N L A then (direct L r A : ℝ) else 0
  let p := fun A : Finset ℕ ↦ if ¬RetainedGoodEdges.Retained H N L A then (pair H N L r A : ℝ) else 0
  have hf := ActiveSetCylinder.observable_integrable G L f
  have hg := ActiveSetCylinder.observable_integrable G L g
  have hd := ActiveSetCylinder.observable_integrable G L d
  have hp := ActiveSetCylinder.observable_integrable G L p
  have hfg : Integrable (fun ω ↦ f (activeSet G L ω) + g (activeSet G L ω)) infiniteRademacherMeasure := hf.add hg
  have hfgd : Integrable (fun ω ↦ f (activeSet G L ω) + g (activeSet G L ω) - d (activeSet G L ω)) infiniteRademacherMeasure := hfg.sub hd
  have hpoint (ω : InfiniteSample) : ((modified H N L G ω).choose r : ℝ) =
      f (activeSet G L ω) + g (activeSet G L ω) - d (activeSet G L ω) - p (activeSet G L ω) := pointwise H N L r hr ω
  unfold modifiedChooseMoment
  change (∫ ω, ((modified H N L G ω).choose r : ℝ) ∂infiniteRademacherMeasure) = _
  simp_rw [hpoint]
  rw [integral_sub hfgd hp, integral_sub hfg hd, integral_add hf hg]
  rfl

theorem directLeakage_nonneg (H : ℝ) (N L r : ℕ) : 0 ≤ directLeakage H N L r := by
  unfold directLeakage
  apply integral_nonneg
  intro ω
  change 0 ≤ if ¬retainedActive H N L (regularStarts N L) ω then (direct L r (activeSet (regularStarts N L) L ω) : ℝ) else 0
  split_ifs <;> positivity

theorem pairLeakage_nonneg (H : ℝ) (N L r : ℕ) : 0 ≤ pairLeakage H N L r := by
  unfold pairLeakage
  apply integral_nonneg
  intro ω
  change 0 ≤ if ¬retainedActive H N L (regularStarts N L) ω then (pair H N L r (activeSet (regularStarts N L) L ω) : ℝ) else 0
  split_ifs <;> positivity

theorem pairMean_nonneg (H : ℝ) (N L r : ℕ) : 0 ≤ pairMean H N L r := integral_nonneg fun _ω ↦ Nat.cast_nonneg _

theorem pairLeakage_le_mean (H : ℝ) (N L r : ℕ) : pairLeakage H N L r ≤ pairMean H N L r := by
  apply integral_mono
    (ActiveSetCylinder.observable_integrable (regularStarts N L) L
      (fun A ↦ if ¬RetainedGoodEdges.Retained H N L A then (pair H N L r A : ℝ) else 0))
    (ActiveSetCylinder.observable_integrable (regularStarts N L) L (fun A ↦ (pair H N L r A : ℝ)))
  intro ω
  change (if ¬RetainedGoodEdges.Retained H N L (activeSet (regularStarts N L) L ω) then
    (pair H N L r (activeSet (regularStarts N L) L ω) : ℝ) else 0) ≤ _
  by_cases h : RetainedGoodEdges.Retained H N L (activeSet (regularStarts N L) L ω) <;> simp [h]

theorem pairLeakage_zero_small (H : ℝ) (N L r : ℕ) (hr : r < 2) : pairLeakage H N L r = 0 :=
  le_antisymm ((pairLeakage_le_mean H N L r).trans_eq (pair_mean_small H N L r hr)) (pairLeakage_nonneg H N L r)

theorem pairMean_zero_large (H : ℝ) (N L r : ℕ) (hr : (regularStarts N L).card < r) : pairMean H N L r = 0 := by
  unfold pairMean
  have hz (ω : InfiniteSample) : pair H N L r (activeSet (regularStarts N L) L ω) = 0 := by
    apply sum_eq_zero
    intro e _he
    have hsub : (activeSet (regularStarts N L) L ω).card ≤ (regularStarts N L).card := card_le_card (filter_subset _ _)
    exact Nat.eq_zero_of_le_zero ((RetainedSubsetCounts.compressedCount_le_choose _ _ e r).trans_eq
      (Nat.choose_eq_zero_of_lt (by omega)))
  simp only [hz, Nat.cast_zero, integral_zero]

theorem pairLeakage_zero_large (H : ℝ) (N L r : ℕ) (hr : (regularStarts N L).card < r) : pairLeakage H N L r = 0 :=
  le_antisymm ((pairLeakage_le_mean H N L r).trans_eq (pairMean_zero_large H N L r hr)) (pairLeakage_nonneg H N L r)

theorem source_identity {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (H : ℝ) (r : ℕ) (hr : 1 ≤ r) :
    modifiedChooseMoment H N L r = ((regularStarts N L).card.choose r : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ r -
      firstCoefficient N L r - directLeakage H N L r + pairBinomialTerm H N L r - secondCoefficient H N L r - pairLeakage H N L r := by
  rw [decomposition H N L r hr, direct_mean hN hL, pair_mean hN hL]
  ring

end PaperP1.RetainedModifiedMomentDecomposition
