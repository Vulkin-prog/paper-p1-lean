module

public import PaperP1.Algebra.HomogeneousPolynomialEvaluation
public import PaperP1.Algebra.LastChartPolynomial
public import PaperP1.Algebra.LinearPolynomialSubstitutionDegree
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # A fixed-degree nonzero homogeneous polynomial remains nonzero in its literal last affine chart -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousLastChartNonzero

open MvPolynomial
open scoped Classical

theorem map_chart {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) R) :
    map φ (LastChartPolynomial.dehomogenize P) = LastChartPolynomial.dehomogenize (map φ P) := by
  have he : (MvPolynomial.map φ).comp (LastChartPolynomial.dehomogenize (R := R) (n := n)) =
      (LastChartPolynomial.dehomogenize (R := S) (n := n)).comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [LastChartPolynomial.dehomogenize]
    · intro i
      cases i using Fin.lastCases <;> simp [LastChartPolynomial.dehomogenize]
  exact RingHom.congr_fun he P

theorem exists_eval_snoc_one {F : Type*} [Field F] [Infinite F] {n d : ℕ}
    (P : MvPolynomial (Fin (n + 1)) F) (hP : P.IsHomogeneous d) (hP0 : P ≠ 0) :
    ∃ v : Fin n → F, eval (Fin.snoc v 1) P ≠ 0 := by
  have hprod : P * X (Fin.last n) ≠ 0 := mul_ne_zero hP0 (X_ne_zero _)
  obtain ⟨v, hv⟩ : ∃ v : Fin (n + 1) → F, eval v (P * X (Fin.last n)) ≠ 0 := by
    by_contra! hh
    exact hprod ((hP.mul (isHomogeneous_X F _)).eq_zero_of_forall_eval_eq_zero hh)
  simp only [map_mul, eval_X] at hv
  obtain ⟨hPv, hvn⟩ := mul_ne_zero_iff.mp hv
  let w (i : Fin n) := (v (Fin.last n))⁻¹ * v i.castSucc
  have he : (fun i ↦ (v (Fin.last n))⁻¹ * v i) = Fin.snoc w 1 := by
    funext i
    cases i using Fin.lastCases with
    | last => simp only [Fin.snoc_last, inv_mul_cancel₀ hvn]
    | cast i => simp only [Fin.snoc_castSucc]; rfl
  refine ⟨w, ?_⟩
  rw [← he, HomogeneousPolynomialEvaluation.eval_scale P hP]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hvn)) hPv

theorem chart_ne_zero {F : Type*} [Field F] {n d : ℕ}
    (P : MvPolynomial (Fin (n + 1)) F) (hP : P.IsHomogeneous d) (hP0 : P ≠ 0) :
    LastChartPolynomial.dehomogenize P ≠ 0 := by
  let φ := algebraMap F (AlgebraicClosure F)
  have hn : map φ P ≠ 0 := by
    intro hh
    exact hP0 (map_injective φ φ.injective (hh.trans (map_zero _).symm))
  obtain ⟨v, hv⟩ := exists_eval_snoc_one (map φ P) (hP.map φ) hn
  intro hz
  have he : LastChartPolynomial.dehomogenize (map φ P) = 0 := by rw [← map_chart, hz, map_zero]
  have hh := congrArg (eval v) he
  apply hv
  simpa only [LastChartPolynomial.evaluation, map_zero] using hh

theorem chart_degree_le {F : Type*} [CommRing F] {n d : ℕ}
    (P : MvPolynomial (Fin (n + 1)) F) (hP : P.IsHomogeneous d) :
    (LastChartPolynomial.dehomogenize P).totalDegree ≤ d := by
  have hh := LinearPolynomialSubstitutionDegree.substitution_bound (RingHom.id F)
    (Fin.snoc X 1 : Fin (n + 1) → MvPolynomial (Fin n) F) (by
      intro i
      cases i using Fin.lastCases with
      | last => simp
      | cast i => simpa only [Fin.snoc_castSucc] using (isHomogeneous_X F i).totalDegree_le) P
  exact hh.trans hP.totalDegree_le

end PaperP1.HomogeneousLastChartNonzero
