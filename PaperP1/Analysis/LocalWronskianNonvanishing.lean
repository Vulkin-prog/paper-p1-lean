module

public import PaperP1.Analysis.LocalLinearIndependence
public import Mathlib.Topology.Order.Basic

/-! # Local linear independence forces actual Wronskian nonvanishing

Smoothness and independence on every open subinterval suffice.
The argument constructs a smaller interval with a nonzero first pivot.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalWronskianNonvanishing

open Set Filter AnalyticWronskianProduct AnalyticWronskianNormalization
open scoped Topology ContDiff

theorem exists_nonzero (n : ℕ) (a b : ℝ) (hab : a < b) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (Ioo a b))
    (hind : LocalLinearIndependence.Independent f (Ioo a b)) :
    ∃ x ∈ Ioo a b, wronskian n f x ≠ 0 := by
  induction n generalizing a b with
  | zero =>
    refine ⟨(a + b) / 2, ⟨by linarith, by linarith⟩, ?_⟩
    simp [wronskian]
  | succ n ih =>
    obtain ⟨x, hx, hxnon⟩ := LocalLinearIndependence.first_nonzero n a b hab f hind
    have hcont : ContinuousAt (f 0) x := (hf 0).continuousOn.continuousAt (isOpen_Ioo.mem_nhds hx)
    have hnb : {t : ℝ | t ∈ Ioo a b ∧ f 0 t ≠ 0} ∈ 𝓝 x :=
      Filter.inter_mem (isOpen_Ioo.mem_nhds hx) (hcont.eventually_ne hxnon)
    obtain ⟨u, v, hxuv, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnb
    have huv : u < v := hxuv.1.trans hxuv.2
    have hinterval : Ioo u v ⊆ Ioo a b := fun t ht ↦ (hsub ht).1
    have hpivot : ∀ t ∈ Ioo u v, f 0 t ≠ 0 := fun t ht ↦ (hsub ht).2
    have hsmall : ∀ i, ContDiffOn ℝ ∞ (f i) (Ioo u v) := fun i ↦ (hf i).mono hinterval
    have hlocal : LocalLinearIndependence.Independent f (Ioo u v) :=
      LocalLinearIndependence.mono f (Ioo a b) (Ioo u v) hind hinterval
    have hg : ∀ i : Fin n, ContDiffOn ℝ ∞ (RecursiveChebyshev.normalizedDerivative f i) (Ioo u v) := by
      intro i
      exact ((hsmall i.succ).div (hsmall 0) hpivot).deriv_of_isOpen isOpen_Ioo (by simp)
    have hgind : LocalLinearIndependence.Independent (RecursiveChebyshev.normalizedDerivative f) (Ioo u v) :=
      LocalLinearIndependence.normalized_independent n u v f
        (fun i ↦ (hsmall i).differentiableOn (by simp)) hpivot hlocal
    obtain ⟨y, hy, hynon⟩ := ih u v huv (RecursiveChebyshev.normalizedDerivative f) hg hgind
    refine ⟨y, hinterval hy, ?_⟩
    rw [wronskian_normalized n f (Ioo u v) isOpen_Ioo
      (fun i ↦ (hsmall i).of_le (by simp)) hpivot y hy]
    exact mul_ne_zero (pow_ne_zero _ (hpivot y hy)) hynon

theorem exists_on_subinterval (n : ℕ) (f : Fin n → ℝ → ℝ) (s : Set ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) s) (hind : LocalLinearIndependence.Independent f s)
    (a b : ℝ) (hab : a < b) (hsub : Ioo a b ⊆ s) :
    ∃ x ∈ Ioo a b, wronskian n f x ≠ 0 :=
  exists_nonzero n a b hab f (fun i ↦ (hf i).mono hsub)
    (LocalLinearIndependence.mono f s (Ioo a b) hind hsub)

end PaperP1.LocalWronskianNonvanishing
