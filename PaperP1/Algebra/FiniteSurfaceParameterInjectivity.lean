module

public import PaperP1.Algebra.HomogeneousFiniteParameterDescent
public import PaperP1.Algebra.TwoParameterIntegralHilbertSlope

/-! # Three finite linear parameters in an actual surface algebra are algebraically independent -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteSurfaceParameterInjectivity

open Polynomial

theorem injective {F A : Type*} [Field F] [Infinite F] [CommRing A] [IsDomain A] [Algebra F A]
    (H : ℕ → Submodule F A) [GradedAlgebra H] [∀ n, Module.Finite F (H n)]
    (p : ℚ[X]) (hp : GradedHilbertPolynomial.IsHilbertPolynomial H p) (hcoeff : p.coeff 2 ≠ 0)
    (g : Fin 3 → A) (hg : ∀ i, g i ∈ H 1) (hfinite : (MvPolynomial.aeval (R := F) g).Finite) :
    Function.Injective (MvPolynomial.aeval (R := F) g) := by
  by_contra hbad
  obtain ⟨u, hu, hufinite⟩ := HomogeneousFiniteParameterDescent.exists_fewer_parameters H g hg hfinite hbad
  obtain ⟨d, β, hline⟩ := TwoParameterIntegralHilbertSlope.of_finite H u hu hufinite
  have he := GradedHilbertPolynomial.unique hp hline
  have hc := congrArg (fun q : ℚ[X] ↦ q.coeff 2) he
  apply hcoeff
  simpa using hc

end PaperP1.FiniteSurfaceParameterInjectivity
