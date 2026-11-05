module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.GroupWithZero.NeZero

/-! # Actual point evaluations agreeing on the image ring are equal away from a conductor denominator -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConductorFiberInjectivity

theorem evaluations_equal {F A Ω : Type*} [CommRing F] [CommRing A] [Field Ω]
    [Algebra F A] [Algebra F Ω] (S : Subalgebra F A) (δ : A)
    (hconductor : ∀ a : A, δ * a ∈ S) (φ ψ : A →ₐ[F] Ω)
    (hagrees : ∀ a ∈ S, φ a = ψ a) (hδ : φ δ ≠ 0) : φ = ψ := by
  have hδS : δ ∈ S := by simpa only [mul_one] using hconductor 1
  apply AlgHom.ext
  intro a
  apply mul_left_cancel₀ hδ
  calc
    φ δ * φ a = φ (δ * a) := (map_mul φ δ a).symm
    _ = ψ (δ * a) := hagrees _ (hconductor a)
    _ = ψ δ * ψ a := map_mul ψ δ a
    _ = φ δ * ψ a := by rw [hagrees δ hδS]

end PaperP1.ConductorFiberInjectivity
