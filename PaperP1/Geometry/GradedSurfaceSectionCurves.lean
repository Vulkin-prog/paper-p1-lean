module

public import PaperP1.Geometry.GradedSurfaceSectionCurveBudget

/-! # Actual surface section components construct one fixed bounded-degree curve family on every normalized chart -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedSurfaceSectionCurves

open Polynomial

theorem exists_family {F A : Type*} [Field F] [Infinite F] [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Algebra F A] (H : ℕ → Submodule F A) [GradedAlgebra H] [∀ n, Module.Finite F (H n)]
    (g : Fin 3 → A) (hg : ∀ i, g i ∈ H 1) (hfinite : (MvPolynomial.aeval (R := F) g).Finite)
    (hinj : Function.Injective (MvPolynomial.aeval (R := F) g))
    (p : ℚ[X]) (hpdeg : p.natDegree ≤ 2) (hp : GradedHilbertPolynomial.IsHilbertPolynomial H p)
    (d : ℕ) (hcoeff : p.coeff 2 = (d : ℚ) / 2)
    (e : ℕ) (f : A) (hf : f ∈ H e) (hf0 : f ≠ 0) (b : A) (hb : b ∈ H 1) :
    ∃ family : Finset (GradedProjectiveCurveData.Curve H),
      family.card ≤ e * d ∧ (∀ Γ ∈ family, f ∈ Γ.ideal ∧ Γ.degree ≤ ((e * d : ℕ) : ℚ)) ∧
      ∀ φ : A →ₐ[F] F, φ f = 0 → φ b ≠ 0 → ∃ Γ ∈ family, Γ.ideal ≤ RingHom.ker φ.toRingHom := by
  obtain ⟨family, hcard, hdegrees, _hsum, hcover⟩ := GradedSurfaceSectionCurveBudget.exists_family
    H g hg hfinite hinj p hpdeg hp d hcoeff e f hf hf0 b hb
  exact ⟨family, hcard, hdegrees, hcover⟩

end PaperP1.GradedSurfaceSectionCurves
