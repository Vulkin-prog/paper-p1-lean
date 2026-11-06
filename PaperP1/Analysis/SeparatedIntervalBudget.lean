module

public import PaperP1.Analysis.LocalSquareSampling

/-! # Actual disjoint sampling intervals and finite sampled square sums -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SeparatedIntervalBudget
open Finset MeasureTheory Set PaperP1
open scoped Classical

theorem unit_intervals_disjoint {ι : Type*} (S : Finset ι) (τ : ι → ℝ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |τ i - τ j|) :
    Set.Pairwise (↑S) (fun i j ↦ Disjoint (Ioc (τ i) (τ i+1)) (Ioc (τ j) (τ j+1))) := by
  intro i hi j hj hne
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hs := hsep i hi j hj hne
  rcases le_total (τ i) (τ j) with hij | hji
  · rw [abs_of_nonpos (sub_nonpos.mpr hij)] at hs
    have hx1 := hxi.2
    have hx2 := hxj.1
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hji)] at hs
    have hx1 := hxi.1
    have hx2 := hxj.2
    linarith

theorem sum_integrals_le {ι : Type*} (S : Finset ι) (τ : ι → ℝ) (A B : ℝ)
    (hAB : A ≤ B) (hrange : ∀ i ∈ S, A ≤ τ i ∧ τ i+1 ≤ B)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |τ i - τ j|)
    (F : ℝ → ℝ) (hF : Continuous F) (hpos : ∀ x, 0 ≤ F x) :
    (∑ i ∈ S, ∫ x in τ i..τ i+1, F x) ≤ ∫ x in A..B, F x := by
  have hsub : (⋃ i ∈ S, Ioc (τ i) (τ i+1)) ⊆ Ioc A B := by
    intro x hx
    obtain ⟨i,hi,hx⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨(hrange i hi).1.trans_lt hx.1, hx.2.trans (hrange i hi).2⟩
  have hu := integral_biUnion_finset (μ := volume) S (fun i hi ↦ measurableSet_Ioc)
    (unit_intervals_disjoint S τ hsep)
    (fun i hi ↦ (hF.intervalIntegrable (τ i) (τ i+1)).1)
  have hm := setIntegral_mono_set (μ := volume) ((hF.intervalIntegrable A B).1)
    (Filter.Eventually.of_forall hpos) hsub.eventuallySubset
  rw [hu] at hm
  have he (i : ι) : (∫ x in τ i..τ i+1, F x) = ∫ x in Ioc (τ i) (τ i+1), F x :=
    intervalIntegral.integral_of_le (by linarith)
  simpa only [he, intervalIntegral.integral_of_le hAB] using hm

theorem sampled_square_bound {ι : Type*} (S : Finset ι) (τ : ι → ℝ) (A B : ℝ)
    (hAB : A ≤ B) (hrange : ∀ i ∈ S, A ≤ τ i ∧ τ i+1 ≤ B)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |τ i - τ j|)
    (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hd : ∀ x, HasDerivAt f (g x) x) :
    (∑ i ∈ S, ‖f (τ i)‖^2) ≤
      2*(∫ x in A..B, ‖f x‖^2) + (∫ x in A..B, ‖g x‖^2) := by
  have hl := sum_le_sum (s := S) (fun i hi ↦ LocalSquareSampling.local_square_bound f g hf hg hd (τ i))
  have hfint := sum_integrals_le S τ A B hAB hrange hsep (fun x ↦ ‖f x‖^2)
    (hf.norm.pow 2) (fun x ↦ sq_nonneg _)
  have hgint := sum_integrals_le S τ A B hAB hrange hsep (fun x ↦ ‖g x‖^2)
    (hg.norm.pow 2) (fun x ↦ sq_nonneg _)
  rw [sum_add_distrib, ← mul_sum] at hl
  linarith

end SeparatedIntervalBudget
