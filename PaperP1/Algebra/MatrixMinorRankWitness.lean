module

public import PaperP1.Algebra.FiniteEvaluationAnnihilator
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! # An actual square minor witnesses every finite matrix rank lower bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MatrixMinorRankWitness

open Finset Submodule
open scoped Classical

theorem exists_minor {K m n : Type*} [Field K] [Fintype m] [Fintype n]
    (A : Matrix m n K) (r : ℕ) (hr : r ≤ A.rank) :
    ∃ c : Fin r → n, ∃ s : Fin r → m, Matrix.det (fun i j ↦ A (s i) (c j)) ≠ 0 := by
  obtain ⟨γ, f, hf, hspan, hli⟩ := exists_linearIndependent' K A.col
  let : Finite γ := Finite.of_injective f hf
  let : Fintype γ := Fintype.ofFinite γ
  have hcard : r ≤ Fintype.card γ := by
    rw [Matrix.rank_eq_finrank_span_cols, ← hspan, finrank_span_eq_card hli] at hr
    exact hr
  let e := Fintype.equivFin γ
  let g : Fin r → γ := fun i ↦ e.symm ⟨i.val, lt_of_lt_of_le i.isLt hcard⟩
  have hg : Function.Injective g := by
    intro i j he
    apply Fin.ext
    have hh := congrArg (fun x : γ ↦ (e x).val) he
    simpa only [g, Equiv.apply_symm_apply] using hh
  let c : Fin r → n := f ∘ g
  have hcols : LinearIndependent K (fun j : Fin r ↦ A.col (c j)) := by
    simpa only [Function.comp_def, c] using hli.comp g hg
  by_contra hn
  have hdet : ∀ s : Fin r → m, Matrix.det (fun i j ↦ A (s i) (c j)) = 0 := by
    intro s
    exact Classical.not_not.mp (fun h ↦ hn ⟨c, s, h⟩)
  obtain ⟨w, hw, hz⟩ := FiniteEvaluationAnnihilator.coefficients
    (fun (i : m) (j : Fin r) ↦ A i (c j)) (by
      intro s _hs
      exact hdet s)
  have hsum : (∑ j : Fin r, w j • A.col (c j)) = 0 := by
    funext i
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply,
      Pi.zero_apply, mul_comm] using hz i
  apply hw
  funext j
  exact (linearIndependent_iff'.mp hcols) univ w hsum j (mem_univ j)

theorem rank_lt_of_all_minors_zero {K m n : Type*} [Field K] [Fintype m] [Fintype n]
    (A : Matrix m n K) (r : ℕ)
    (h : ∀ (c : Fin r → n) (s : Fin r → m), Matrix.det (fun i j ↦ A (s i) (c j)) = 0) :
    A.rank < r := by
  by_contra hn
  obtain ⟨c, s, hne⟩ := exists_minor A r (Nat.le_of_not_gt hn)
  exact hne (h c s)

end PaperP1.MatrixMinorRankWitness
