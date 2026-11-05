module

public import PaperP1.Algebra.ScalarExtendedGradedHilbert
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-! # Nilpotence of the actual zero-fibre generators descends faithfully through a coefficient-field extension -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScalarExtendedFiniteFiber

open scoped TensorProduct

theorem power_zero_iff {F E A : Type*} [Field F] [Field E] [Algebra F E]
    [CommRing A] [Algebra F A] (a : A) (N : ℕ) :
    (((1 : E) ⊗ₜ[F] a) ^ N = 0) ↔ a ^ N = 0 := by
  let ι : A →ₐ[F] E ⊗[F] A := Algebra.TensorProduct.includeRight
  have hinj : Function.Injective ι :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F E).injective
  constructor
  · intro hh
    apply hinj
    rw [map_pow, map_zero]
    exact hh
  · intro hh
    change ι a ^ N = 0
    rw [← map_pow, hh, map_zero]

theorem finite_of_generator_powers {F A σ : Type*} [Field F] [CommRing A] [Algebra F A] [Finite σ]
    (x : σ → A) (hgen : Algebra.adjoin F (Set.range x) = ⊤) (N : ℕ) (hN : 0 < N)
    (hpow : ∀ i, x i ^ N = 0) : Module.Finite F A := by
  have hint (i : σ) : IsIntegral F (x i) := by
    apply IsIntegral.of_pow hN
    rw [hpow i]
    exact isIntegral_zero
  let : Module.Finite F (Algebra.adjoin F (Set.range x)) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range x) (by
      rintro _ ⟨i, rfl⟩
      exact hint i)
  exact Module.Finite.of_surjective (Algebra.adjoin F (Set.range x)).val.toLinearMap (by
    intro a
    exact ⟨⟨a, by rw [hgen]; trivial⟩, rfl⟩)

theorem finite_of_scalar_generator_powers {F E A σ : Type*} [Field F] [Field E] [Algebra F E]
    [CommRing A] [Algebra F A] [Finite σ]
    (x : σ → A) (hgen : Algebra.adjoin F (Set.range x) = ⊤) (N : ℕ) (hN : 0 < N)
    (hpow : ∀ i, ((1 : E) ⊗ₜ[F] x i) ^ N = 0) : Module.Finite F A := by
  exact finite_of_generator_powers x hgen N hN (fun i ↦ (power_zero_iff (E := E) (x i) N).mp (hpow i))

end PaperP1.ScalarExtendedFiniteFiber
