module

public import PaperP1.Algebra.TwoParameterIntegralHilbertSlope
public import PaperP1.Algebra.GradedPolynomialCoordinateImage

/-! # The actual linear coordinate image has a nonnegative integral linear Hilbert coefficient at most the original one -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearCoordinateCurveImageDegree

open GradedPolynomialCoordinateImage

theorem exists_nat_linear_hilbert {F R σ : Type*} [Field F] [Infinite F] [CommRing R] [IsDomain R]
    [Algebra F R] [Finite σ] (H : ℕ → Submodule F R) [GradedAlgebra H]
    [∀ n, Module.Finite F (H n)] (a b : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial H (Polynomial.C a * Polynomial.X + Polynomial.C b))
    (g : σ → R) (hg : ∀ i, g i ∈ H 1) :
    ∃ (d : ℕ) (β : ℚ), GradedHilbertPolynomial.IsHilbertPolynomial (piece (F := F) g)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C β) ∧ (d : ℚ) ≤ a := by
  let : (RingHom.ker (MvPolynomial.aeval (R := F) g)).IsPrime := RingHom.ker_isPrime _
  let := grading H g hg
  let f := gradedToSource H g hg
  let (n : ℕ) : Module.Finite F (piece (F := F) g n) := Module.Finite.of_injective
    (GradedInjectiveHilbertComparison.pieceMap f (fun r ↦ (toSource (F := F) g).commutes r) n)
    (GradedInjectiveHilbertComparison.pieceMap_injective f (fun r ↦ (toSource (F := F) g).commutes r)
      (toSource_injective (F := F) g) n)
  obtain ⟨u, hu, hufinite⟩ := exists_finite_parameters H a b hp g hg
  obtain ⟨d, β, hd⟩ := TwoParameterIntegralHilbertSlope.of_finite (piece (F := F) g) u hu hufinite
  have hle := GradedInjectiveHilbertComparison.linear_degree_le f
    (fun r ↦ (toSource (F := F) g).commutes r) (toSource_injective (F := F) g) (d : ℚ) β a b hd hp
  exact ⟨d, β, hd, hle⟩

end PaperP1.LinearCoordinateCurveImageDegree
