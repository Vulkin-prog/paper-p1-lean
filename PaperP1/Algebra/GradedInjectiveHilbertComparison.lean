module

public import PaperP1.Algebra.GradedModulePieceMap
public import PaperP1.Algebra.GradedHilbertPolynomial
public import PaperP1.Algebra.PolynomialEventualCoefficientOrder
public import Mathlib.Tactic.ComputeDegree

/-! # Actual injective graded algebra maps compare genuine Hilbert coefficients -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedInjectiveHilbertComparison

open Polynomial

variable {F A B : Type*} [Field F] [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
  {G : ℕ → Submodule F A} {H : ℕ → Submodule F B}
  (f : G →+*ᵍ H) (hscalar : ∀ a : F, f (algebraMap F A a) = algebraMap F B a)

def pieceMap (n : ℕ) : G n →ₗ[F] H n where
  toFun a := ⟨f a, f.map_mem a.property⟩
  map_add' a b := Subtype.ext (map_add f (a : A) (b : A))
  map_smul' r a := Subtype.ext ((GradedModulePieceMap.algHom f hscalar).toLinearMap.map_smul r (a : A))

include hscalar

theorem pieceMap_injective (hinj : Function.Injective f) (n : ℕ) :
    Function.Injective (pieceMap f hscalar n) := by
  intro a b he
  exact Subtype.ext (hinj (congrArg Subtype.val he))

theorem dimension_le (hinj : Function.Injective f) (n : ℕ) [Module.Finite F (H n)] :
    Module.finrank F (G n) ≤ Module.finrank F (H n) :=
  LinearMap.finrank_le_finrank_of_injective (f := pieceMap f hscalar n) (pieceMap_injective f hscalar hinj n)

theorem coefficient_le [∀ n, Module.Finite F (H n)] (hinj : Function.Injective f)
    (p q : ℚ[X]) (r : ℕ) (hpdeg : p.natDegree ≤ r) (hqdeg : q.natDegree ≤ r)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial G p)
    (hq : GradedHilbertPolynomial.IsHilbertPolynomial H q) : p.coeff r ≤ q.coeff r := by
  obtain ⟨N, hN⟩ := hp
  obtain ⟨M, hM⟩ := hq
  apply PolynomialEventualCoefficientOrder.coefficient_le p q r hpdeg hqdeg (max N M)
  intro n hn
  rw [hN n ((le_max_left _ _).trans hn), hM n ((le_max_right _ _).trans hn)]
  exact_mod_cast dimension_le f hscalar hinj n

theorem linear_degree_le [∀ n, Module.Finite F (H n)] (hinj : Function.Injective f)
    (d b e β : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial G (C d * X + C b))
    (hq : GradedHilbertPolynomial.IsHilbertPolynomial H (C e * X + C β)) : d ≤ e := by
  have hh := coefficient_le f hscalar hinj _ _ 1 (by compute_degree) (by compute_degree) hp hq
  simpa only [coeff_add, coeff_C_mul, coeff_X_one, coeff_C_succ, mul_one, add_zero] using hh

end PaperP1.GradedInjectiveHilbertComparison
