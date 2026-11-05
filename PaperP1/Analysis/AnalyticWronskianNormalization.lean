module

public import PaperP1.Analysis.AnalyticWronskianProduct
public import PaperP1.Analysis.RecursiveChebyshev

/-! # The classical Wronskian identity for normalized derivative families

All quotients and derivative congruences are restricted to the actual open set
where the first function is nonzero.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnalyticWronskianNormalization

open Finset Set AnalyticWronskianProduct

theorem wronskian_congr_on (n : ℕ) (f g : Fin n → ℝ → ℝ) (s : Set ℝ) (hs : IsOpen s)
    (hfg : ∀ i, EqOn (f i) (g i) s) (x : ℝ) (hx : x ∈ s) :
    wronskian n f x = wronskian n g x := by
  change (jetMatrix n f x).det = (jetMatrix n g x).det
  congr 1
  ext i j
  exact (hfg j).iteratedDeriv_of_isOpen hs i.val hx

theorem wronskian_one_tail (n : ℕ) (f : Fin n → ℝ → ℝ) (x : ℝ) :
    wronskian (n + 1) (Fin.cons (fun _ ↦ 1) f) x = wronskian n (fun i ↦ deriv (f i)) x := by
  simp [wronskian, Matrix.det_succ_column_zero, jetMatrix,
    iteratedDeriv_const, Fin.succAbove_zero]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, jetMatrix, Fin.cons_succ, Fin.val_succ, iteratedDeriv_succ']

theorem wronskian_normalized (n : ℕ) (f : Fin (n + 1) → ℝ → ℝ)
    (s : Set ℝ) (hs : IsOpen s) (hf : ∀ i, ContDiffOn ℝ (n + 1) (f i) s)
    (hnon : ∀ x ∈ s, f 0 x ≠ 0) (x : ℝ) (hx : x ∈ s) :
    wronskian (n + 1) f x = f 0 x ^ (n + 1) *
      wronskian n (RecursiveChebyshev.normalizedDerivative f) x := by
  let g : Fin n → ℝ → ℝ := fun i t ↦ f i.succ t / f 0 t
  let h : Fin (n + 1) → ℝ → ℝ := Fin.cons (fun _ ↦ 1) g
  have hh : ∀ i, ContDiffOn ℝ (n + 1) (h i) s := by
    intro i
    refine Fin.cases (by exact contDiffOn_const) (fun j ↦ ?_) i
    exact (hf j.succ).div (hf 0) hnon
  have heq : ∀ i, EqOn (f i) (fun t ↦ f 0 t * h i t) s := by
    intro i t ht
    refine Fin.cases (by simp [h]) (fun j ↦ ?_) i
    change f j.succ t = f 0 t * (f j.succ t / f 0 t)
    field_simp [hnon t ht]
  calc
    _ = wronskian (n + 1) (fun i t ↦ f 0 t * h i t) x := wronskian_congr_on _ _ _ s hs heq x hx
    _ = f 0 x ^ (n + 1) * wronskian (n + 1) h x :=
      wronskian_product (n + 1) (f 0) h x ((hf 0).contDiffAt (hs.mem_nhds hx))
        (fun i ↦ (hh i).contDiffAt (hs.mem_nhds hx))
    _ = _ := by rw [wronskian_one_tail]; rfl

end PaperP1.AnalyticWronskianNormalization
