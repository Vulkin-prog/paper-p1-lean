module

public import PaperP1.Algebra.BiquadraticNorm

/-! # The literal norm formula with the overlap quotient appearing in the manuscript -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.BiquadraticSourceNorm

def sourceNorm {R : Type*} [CommRing R] (f₁ f₂ f₃ h a b c d : R) : R :=
  (a ^ 2 + f₁ * b ^ 2 - f₂ * c ^ 2 - f₃ * d ^ 2) ^ 2 -
    4 * f₁ * (a * b - h * c * d) ^ 2

theorem map_sourceNorm {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (f₁ f₂ f₃ h a b c d : R) :
    φ (sourceNorm f₁ f₂ f₃ h a b c d) =
      sourceNorm (φ f₁) (φ f₂) (φ f₃) (φ h) (φ a) (φ b) (φ c) (φ d) := by
  simp only [sourceNorm, map_sub, map_add, map_pow, map_mul, map_ofNat]

theorem sourceNorm_normalized {F : Type*} [Field F] (f₁ f₂ f₃ h g a b c d : F)
    (hg : g ≠ 0) (h₃ : f₃ * g ^ 2 = f₁ * f₂) (hh : h * g = f₂) :
    sourceNorm f₁ f₂ f₃ h a b c d = BiquadraticNorm.norm f₁ f₂ a b c (d / g) := by
  have he₃ : f₃ = f₁ * f₂ / g ^ 2 := (eq_div_iff (pow_ne_zero 2 hg)).mpr h₃
  have heh : h = f₂ / g := (eq_div_iff hg).mpr hh
  unfold sourceNorm BiquadraticNorm.norm BiquadraticNorm.upper BiquadraticNorm.mixed
  rw [he₃, heh]
  field_simp

theorem sourceNorm_ne_zero {F : Type*} [Field F] [CharZero F] (f₁ f₂ f₃ h g a b c d : F)
    (hg : g ≠ 0) (h₃ : f₃ * g ^ 2 = f₁ * f₂) (hh : h * g = f₂)
    (hf₁ : ¬ IsSquare f₁) (hf₂ : ¬ IsSquare f₂) (hf₁₂ : ¬ IsSquare (f₁ * f₂))
    (hne : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) : sourceNorm f₁ f₂ f₃ h a b c d ≠ 0 := by
  rw [sourceNorm_normalized f₁ f₂ f₃ h g a b c d hg h₃ hh]
  apply BiquadraticNorm.norm_ne_zero _ _ _ _ _ _ hf₁ hf₂ hf₁₂
  rcases hne with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (div_ne_zero h hg)))

theorem sourceNorm_zero_of_auxiliary {R : Type*} [CommRing R]
    (f₁ f₂ f₃ h a b c d w₁ w₂ w₃ : R)
    (h₁ : w₁ ^ 2 = f₁) (h₂ : w₂ ^ 2 = f₂) (h₃ : w₃ ^ 2 = f₃)
    (h₂₃ : w₂ * w₃ = w₁ * h) (haux : a + b * w₁ + c * w₂ + d * w₃ = 0) :
    sourceNorm f₁ f₂ f₃ h a b c d = 0 := by
  have hid : (a ^ 2 + f₁ * b ^ 2 - f₂ * c ^ 2 - f₃ * d ^ 2) +
      2 * w₁ * (a * b - h * c * d) =
        (a + b * w₁ + c * w₂ + d * w₃) * (a + b * w₁ - c * w₂ - d * w₃) := by
    linear_combination -(b ^ 2) * h₁ + (c ^ 2) * h₂ + (d ^ 2) * h₃ + (2 * c * d) * h₂₃
  rw [haux, zero_mul] at hid
  have hu : a ^ 2 + f₁ * b ^ 2 - f₂ * c ^ 2 - f₃ * d ^ 2 =
      -(2 * w₁ * (a * b - h * c * d)) := by linear_combination hid
  unfold sourceNorm
  rw [hu]
  linear_combination (4 * (a * b - h * c * d) ^ 2) * h₁

theorem mixed_of_overlap {R : Type*} [CommRing R] [IsDomain R]
    (g h f₂ w₁ w₂ w₃ : R) (hg : g ≠ 0) (hh : g * h = f₂)
    (h₂ : w₂ ^ 2 = f₂) (h₃ : g * w₃ = w₁ * w₂) : w₂ * w₃ = w₁ * h := by
  apply mul_left_cancel₀ hg
  linear_combination w₂ * h₃ + w₁ * h₂ - w₁ * hh

end PaperP1.BiquadraticSourceNorm
