module

public import PaperP1.Geometry.FiniteParameterCurveEquation
public import PaperP1.Algebra.HomogeneousFiniteParameterDescent
public import PaperP1.Algebra.TwoParameterIntegralHilbertSlope

/-! # Actual height-one primes in a finitely normalized surface construct their own positive integral curve Hilbert degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteSurfaceCurveHilbert

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_nat_linear_hilbert {F A : Type*} [Field F] [Infinite F] [CommRing A] [IsDomain A] [Algebra F A]
    (H : ℕ → Submodule F A) [GradedAlgebra H] [∀ n, Module.Finite F (H n)]
    (g : Fin 3 → A) (hg : ∀ i, g i ∈ H 1) (hfinite : (aeval (R := F) g).Finite)
    (hinj : Function.Injective (aeval (R := F) g))
    (Q : Ideal A) [Q.IsPrime] (hQ : Q.IsHomogeneous H) (hheight : Q.height = 1) :
    ∃ (d : ℕ) (β : ℚ), 0 < d ∧ GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece H Q) (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C β) := by
  let f := GradedPolynomialGenerators.gradedEval H g hg
  let P := Q.comap (aeval (R := F) g).toRingHom
  have hP : P.IsHomogeneous (homogeneousSubmodule (Fin 3) F) :=
    GradedQuotientModuleGenerators.baseIdeal_homogeneous f Q hQ
  have hPheight : P.height = 1 := (FiniteParameterCurveEquation.contracted_height g hfinite hinj Q).trans hheight
  let : P.IsPrime := Ideal.IsPrime.comap (aeval (R := F) g).toRingHom
  obtain ⟨e, h, he, hh0, hh, hspan⟩ := HomogeneousHeightOneEquation.exists_equation P hP hPheight
  let := HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin 3) F) P hP
  let : GradedAlgebra (HomogeneousQuotientGrading.piece H Q) := HomogeneousQuotientGrading.grading H Q hQ
  let (n : ℕ) : Module.Finite F (HomogeneousQuotientGrading.piece H Q n) :=
    HomogeneousQuotientGrading.piece_finite H Q n
  let gQ : Fin 3 → (A ⧸ Q) := fun i ↦ Ideal.Quotient.mk Q (g i)
  have hgQ (i : Fin 3) : gQ i ∈ HomogeneousQuotientGrading.piece H Q 1 :=
    Submodule.mem_map.mpr ⟨g i, hg i, rfl⟩
  have hcomp : aeval (R := F) gQ = (Ideal.Quotient.mkₐ F Q).comp (aeval (R := F) g) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, aeval_X]
    rfl
  have hQfinite : (aeval (R := F) gQ).Finite := by
    rw [hcomp]
    exact AlgHom.Finite.comp (AlgHom.Finite.of_surjective (Ideal.Quotient.mkₐ F Q) Ideal.Quotient.mk_surjective) hfinite
  have hbad : ¬ Function.Injective (aeval (R := F) gQ) := by
    intro hi
    have hz : aeval (R := F) gQ h = 0 := by
      rw [hcomp, AlgHom.comp_apply]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change h ∈ P
      rw [hspan]
      exact Ideal.mem_span_singleton_self h
    exact hh0 (hi (by simpa only [map_zero] using hz))
  obtain ⟨u, hu, hufinite⟩ := HomogeneousFiniteParameterDescent.exists_fewer_parameters
    (HomogeneousQuotientGrading.piece H Q) gQ hgQ hQfinite hbad
  obtain ⟨d, β, hd⟩ := TwoParameterIntegralHilbertSlope.of_finite (HomogeneousQuotientGrading.piece H Q) u hu hufinite
  have hplane : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin 3) F) P)
      (Polynomial.C (e : ℚ) * Polynomial.X + Polynomial.C ((3 * (e : ℚ) - (e : ℚ) ^ 2) / 2)) := by
    rw [hspan]
    exact PlaneCurveHilbert.isHilbertPolynomial F h hh hh0
  have hscalar (r : F) : f (algebraMap F (MvPolynomial (Fin 3) F) r) = algebraMap F A r := (aeval (R := F) g).commutes r
  have hle := GradedInjectiveHilbertComparison.linear_degree_le
    (GradedQuotientModuleGenerators.map f Q) (GradedQuotientModuleGenerators.map_commutes f hscalar Q)
    (GradedQuotientModuleGenerators.map_injective f Q) (e : ℚ) _ (d : ℚ) β hplane hd
  have hdpos : (0 : ℚ) < d := (Nat.cast_pos.mpr he).trans_le hle
  exact ⟨d, β, by exact_mod_cast hdpos, hd⟩

end PaperP1.FiniteSurfaceCurveHilbert
