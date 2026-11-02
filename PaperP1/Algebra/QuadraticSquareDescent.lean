module

public import PaperP1.Algebra.BiquadraticNormModel
public import PaperP1.Algebra.FieldSquareClasses

/-! # The exact descent criterion for a base-field square in a quadratic radical algebra -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticSquareDescent

open QuadraticAlgebra PaperP1.BiquadraticNormModel

theorem square_iff {K : Type*} [Field K] [CharZero K] (f g : K) (hf : f ≠ 0) :
    IsSquare (algebraMap K (First K f) g) ↔ IsSquare g ∨ IsSquare (f * g) := by
  classical
  constructor
  · intro hs
    by_cases hg : IsSquare g
    · exact Or.inl hg
    · right
      by_contra hfg
      exact second_nonsquare f g hg hfg hs
  · rintro (hg | hfg)
    · exact IsSquare.map (algebraMap K (First K f)) hg
    · obtain ⟨w, hw⟩ := hfg
      let z : First K f := algebraMap K (First K f) (w / f) * omega
      have hω : (omega : First K f) ^ 2 = algebraMap K (First K f) f := by
        rw [pow_two, omega_mul_omega_eq_algebraMap, map_zero, zero_mul, add_zero]
      have hbase : (w / f) ^ 2 * f = g := by
        calc
          _ = (w * w) / f := by field_simp
          _ = g := by rw [← hw]; field_simp
      have hz : z ^ 2 = algebraMap K (First K f) g := by
        dsimp [z]
        rw [mul_pow, ← map_pow, hω, ← map_mul, hbase]
      exact ⟨z, by simpa only [pow_two] using hz.symm⟩

theorem nonsquare_iff {K : Type*} [Field K] [CharZero K] (f g : K) (hf : f ≠ 0) :
    ¬ IsSquare (algebraMap K (First K f) g) ↔ ¬ IsSquare g ∧ ¬ IsSquare (f * g) := by
  rw [square_iff f g hf, not_or]

end PaperP1.QuadraticSquareDescent
