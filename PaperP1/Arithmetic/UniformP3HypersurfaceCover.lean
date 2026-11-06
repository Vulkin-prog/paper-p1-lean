module

public import PaperP1.Geometry.GradedProjectiveCurveData
public import PaperP1.Geometry.PresentedProjectiveCurveData
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.Pi

/-! # The exact coefficient-uniform P³ hypersurface covering input on actual normalized integer points

`UniformCover` below is an UNPROVED INPUT, not an axiom or a proved surface theorem.
It records the geometric covering conclusion of Salberger, arXiv:2311.05561v1,
Lemma 2, on the fixed normalized chart X₃ = 1. The actual projective curve points,
height-one primes, quotient Hilbert degrees and polynomial-coordinate ideals are
retained. Constants precede all equation coefficients, heights and point subsets.
`PresentedProjectiveCurveData` identifies these degrees with the ordinary projective
coordinate Hilbert degrees. The actual source projection and cover transfer have
already been proved in `ActualSourceSurfaceCoverReduction`.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformP3HypersurfaceCover

open MvPolynomial Finset

attribute [local instance] MvPolynomial.gradedAlgebra

def points (q : MvPolynomial (Fin 4) ℚ) (H : ℕ) : Finset (Fin 4 → ℤ) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin 4 ↦ Icc (-(H : ℤ)) H)).filter
    (fun v ↦ v 3 = 1 ∧ eval (fun i ↦ (v i : ℚ)) q = 0)

theorem mem_points (q : MvPolynomial (Fin 4) ℚ) (H : ℕ) (v : Fin 4 → ℤ) :
    v ∈ points q H ↔ (∀ i, |v i| ≤ (H : ℤ)) ∧ v 3 = 1 ∧ eval (fun i ↦ (v i : ℚ)) q = 0 := by
  classical
  simp only [points, mem_filter, Fintype.mem_piFinset, mem_Icc, ← abs_le]

def CoverAtDegree (d M : ℕ) (A δ : ℝ) : Prop :=
  ∀ (I : Ideal (MvPolynomial (Fin 4) ℚ))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 4) ℚ)),
    letI := HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin 4) ℚ) I hI;
    ∀ q : MvPolynomial (Fin 4) ℚ, I = Ideal.span {q} →
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) q) →
      q.IsHomogeneous d → q.totalDegree = d →
    ∀ H : ℕ, 1 ≤ H → ∀ U : Finset (Fin 4 → ℤ), U ⊆ points q H →
    ∃ (T : Finset (Fin 4 → ℤ))
      (family : Finset (GradedProjectiveCurveData.Curve
        (HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin 4) ℚ) I))),
      T ⊆ U ∧ (∀ Γ ∈ family, Γ.degree ≤ (M : ℚ)) ∧
      (T.card : ℝ) ≤ A * (H : ℝ) ^ (2 / Real.sqrt (d : ℝ) + δ) ∧
      (family.card : ℝ) ≤ A * (H : ℝ) ^ (1 / Real.sqrt (d : ℝ) + δ) ∧
      ∀ v ∈ U, v ∉ T → ∃ Γ ∈ family,
        ∀ P ∈ Γ.ideal.comap (Ideal.Quotient.mk I), eval (fun i ↦ (v i : ℚ)) P = 0

def UniformCover (d : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ (M : ℕ) (A : ℝ), 0 < A ∧ CoverAtDegree d M A δ

theorem CoverAtDegree.mono {d M M' : ℕ} {A A' δ : ℝ}
    (h : CoverAtDegree d M A δ) (hM : M ≤ M') (hA : A ≤ A') : CoverAtDegree d M' A' δ := by
  intro I hI
  let := HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin 4) ℚ) I hI
  intro q hq hgeom hhom hdegree H hH U hU
  obtain ⟨T, family, hT, hdegrees, hTbound, hfbound, hcover⟩ := h I hI q hq hgeom hhom hdegree H hH U hU
  refine ⟨T, family, hT, ?_, ?_, ?_, hcover⟩
  · intro Γ hΓ
    exact (hdegrees Γ hΓ).trans (by exact_mod_cast hM)
  · exact hTbound.trans (mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg (Nat.cast_nonneg H) _))
  · exact hfbound.trans (mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg (Nat.cast_nonneg H) _))

end PaperP1.UniformP3HypersurfaceCover
