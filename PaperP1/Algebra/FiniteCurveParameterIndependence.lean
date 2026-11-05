module

public import PaperP1.Algebra.HomogeneousKernelReduction
public import PaperP1.Algebra.UnivariateFiniteHilbert
public import PaperP1.Algebra.IntegerLinearHilbertSlope

/-! # Positive actual linear Hilbert growth forces finite linear curve parameters to be independent -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteCurveParameterIndependence

open Polynomial

theorem injective {F A : Type*} [Field F] [Infinite F] [CommRing A] [Algebra F A]
    (H : ℕ → Submodule F A) [GradedAlgebra H] [∀ n, Module.Finite F (H n)]
    (g : Fin 2 → A) (hg : ∀ i, g i ∈ H 1) (hfinite : (MvPolynomial.aeval (R := F) g).Finite)
    (a b : ℚ) (ha : 0 < a)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial H (C a * X + C b)) :
    Function.Injective (MvPolynomial.aeval (R := F) g) := by
  by_contra hbad
  obtain ⟨x, hx, hfinx⟩ := HomogeneousKernelReduction.exists_one_parameter H g hg hfinite hbad
  obtain ⟨M, c, hconst⟩ := UnivariateFiniteHilbert.eventually_constant H x hx hfinx
  obtain ⟨N, hpoly⟩ := hp
  have htail (n : ℕ) (hn : N ≤ n) : a * (n : ℚ) + b = (Module.finrank F (H n) : ℚ) := by
    simpa only [eval_add, eval_mul, eval_C, eval_X] using hpoly n hn
  obtain ⟨d, hd, _hcast, hstep⟩ := IntegerLinearHilbertSlope.slope_and_increment
    (fun n ↦ Module.finrank F (H n)) a b ha N htail
  have hs := hstep (max N M) (le_max_left _ _)
  rw [hconst _ (le_max_right _ _), hconst _ ((le_max_right N M).trans (Nat.le_add_right _ 1))] at hs
  omega

end PaperP1.FiniteCurveParameterIndependence
