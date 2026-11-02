module

public import PaperP1.Algebra.BiquadraticSourceNorm
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Lean.Elab.Tactic.Omega

/-! # The sharp degree 4k bound in the literal biquadratic norm formula -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.BiquadraticNormDegree

open Polynomial PaperP1.BiquadraticSourceNorm

theorem weighted_square {R : Type*} [CommRing R] (A F : R[X]) (k r : ℕ)
    (hr : r ≤ k) (hA : A.natDegree ≤ k - r) (hF : F.natDegree ≤ 2 * r) :
    (F * A ^ 2).natDegree ≤ 2 * k := by
  have hp := natDegree_pow_le (p := A) (n := 2)
  have hm := natDegree_mul_le (p := F) (q := A ^ 2)
  omega

theorem upper_bound {R : Type*} [CommRing R] (f₁ f₂ f₃ a b c d : R[X]) (k r₁ r₂ r₃ : ℕ)
    (hr₁ : r₁ ≤ k) (hr₂ : r₂ ≤ k) (hr₃ : r₃ ≤ k)
    (ha : a.natDegree ≤ k) (hb : b.natDegree ≤ k - r₁)
    (hc : c.natDegree ≤ k - r₂) (hd : d.natDegree ≤ k - r₃)
    (hf₁ : f₁.natDegree ≤ 2 * r₁) (hf₂ : f₂.natDegree ≤ 2 * r₂) (hf₃ : f₃.natDegree ≤ 2 * r₃) :
    (a ^ 2 + f₁ * b ^ 2 - f₂ * c ^ 2 - f₃ * d ^ 2).natDegree ≤ 2 * k := by
  have ha₂ : (a ^ 2).natDegree ≤ 2 * k := natDegree_pow_le_of_le 2 ha
  have hab := natDegree_add_le_of_degree_le ha₂ (weighted_square b f₁ k r₁ hr₁ hb hf₁)
  have habc := (natDegree_sub_le _ _).trans (max_le hab (weighted_square c f₂ k r₂ hr₂ hc hf₂))
  exact (natDegree_sub_le _ _).trans (max_le habc (weighted_square d f₃ k r₃ hr₃ hd hf₃))

theorem mixed_bound {R : Type*} [CommRing R] (h a b c d : R[X]) (k r₁ r₂ r₃ : ℕ)
    (hr₁ : r₁ ≤ k) (hr₂ : r₂ ≤ k) (hr₃ : r₃ ≤ k)
    (ha : a.natDegree ≤ k) (hb : b.natDegree ≤ k - r₁)
    (hc : c.natDegree ≤ k - r₂) (hd : d.natDegree ≤ k - r₃)
    (hh : h.natDegree + r₁ ≤ r₂ + r₃) :
    (a * b - h * c * d).natDegree ≤ 2 * k - r₁ := by
  have hab : (a * b).natDegree ≤ 2 * k - r₁ := by
    have he := natDegree_mul_le (p := a) (q := b)
    omega
  have hcd : (h * c * d).natDegree ≤ 2 * k - r₁ := by
    have he₁ := natDegree_mul_le (p := h) (q := c)
    have he₂ := natDegree_mul_le (p := h * c) (q := d)
    omega
  exact (natDegree_sub_le _ _).trans (max_le hab hcd)

theorem norm_bound {R : Type*} [CommRing R] (f₁ f₂ f₃ h a b c d : R[X]) (k r₁ r₂ r₃ : ℕ)
    (hr₁ : r₁ ≤ k) (hr₂ : r₂ ≤ k) (hr₃ : r₃ ≤ k)
    (ha : a.natDegree ≤ k) (hb : b.natDegree ≤ k - r₁)
    (hc : c.natDegree ≤ k - r₂) (hd : d.natDegree ≤ k - r₃)
    (hf₁ : f₁.natDegree ≤ 2 * r₁) (hf₂ : f₂.natDegree ≤ 2 * r₂) (hf₃ : f₃.natDegree ≤ 2 * r₃)
    (hh : h.natDegree + r₁ ≤ r₂ + r₃) :
    (sourceNorm f₁ f₂ f₃ h a b c d).natDegree ≤ 4 * k := by
  have hu := upper_bound f₁ f₂ f₃ a b c d k r₁ r₂ r₃ hr₁ hr₂ hr₃ ha hb hc hd hf₁ hf₂ hf₃
  have hv := mixed_bound h a b c d k r₁ r₂ r₃ hr₁ hr₂ hr₃ ha hb hc hd hh
  have hu₂ : ((a ^ 2 + f₁ * b ^ 2 - f₂ * c ^ 2 - f₃ * d ^ 2) ^ 2).natDegree ≤ 4 * k := by
    have he := natDegree_pow_le (p := a ^ 2 + f₁ * b ^ 2 - f₂ * c ^ 2 - f₃ * d ^ 2) (n := 2)
    omega
  have hfv : (f₁ * (a * b - h * c * d) ^ 2).natDegree ≤ 4 * k := by
    have he₁ := natDegree_pow_le (p := a * b - h * c * d) (n := 2)
    have he₂ := natDegree_mul_le (p := f₁) (q := (a * b - h * c * d) ^ 2)
    omega
  have hfour : ((4 : R[X]) * f₁ * (a * b - h * c * d) ^ 2).natDegree ≤ 4 * k := by
    simpa only [map_ofNat, mul_assoc] using (natDegree_C_mul_le (4 : R) _).trans hfv
  exact (natDegree_sub_le _ _).trans (max_le hu₂ hfour)

end PaperP1.BiquadraticNormDegree
