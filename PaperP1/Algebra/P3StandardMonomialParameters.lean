module

public import PaperP1.Algebra.P3StandardMonomialWeightPolynomial

/-! # Coefficient-independent natural size and height-weight parameters for the actual standard family -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3StandardMonomialParameters

open P3StandardMonomialCount NormalizedP3MonomialHeight
open scoped Classical

def size (d e : ℕ) : ℕ := (e + 3).choose 3 - (e - d + 3).choose 3

def weight (d e : ℕ) : ℕ :=
  (3 * e * (e + 3).choose 3 - (4 * d + 3 * (e - d)) * (e - d + 3).choose 3) / 4

theorem size_eq (μ : Fin 4 →₀ ℕ) (e : ℕ) (he : μ.degree ≤ e) :
    Fintype.card (StandardIndex μ e) = size μ.degree e := cardinality μ e he

theorem weight_eq (μ : Fin 4 →₀ ℕ) (e : ℕ) (he : μ.degree ≤ e) (hμ : μ 3 = 0) :
    (∑ r : StandardIndex μ e, freeDegree r.val.val) = weight μ.degree e := by
  have hs := P3StandardMonomialWeightBudget.scaled_free_budget μ e he hμ
  have hh : 3 * e * (e + 3).choose 3 -
      (4 * μ.degree + 3 * (e - μ.degree)) * (e - μ.degree + 3).choose 3 =
        4 * (∑ r : StandardIndex μ e, freeDegree r.val.val) := by omega
  dsimp only [weight]
  rw [hh, Nat.mul_div_cancel_left _ (by omega : 0 < 4)]

theorem size_polynomial (d e : ℕ) (he : d ≤ e) :
    (size d e : ℚ) = (ProjectiveHypersurfaceHilbert.polynomial d).eval (e : ℚ) := by
  let μ : Fin 4 →₀ ℕ := Finsupp.single 0 d
  have hμdeg : μ.degree = d := Finsupp.degree_single 0 d
  have hme : μ.degree ≤ e := hμdeg ▸ he
  have hs := P3StandardMonomialWeightPolynomial.cardinality_polynomial μ e hme
  rw [size_eq μ e hme, hμdeg] at hs
  exact hs

theorem weight_polynomial (d e : ℕ) (he : d ≤ e) :
    (weight d e : ℚ) = (P3StandardMonomialWeightPolynomial.polynomial d).eval (e : ℚ) := by
  let μ : Fin 4 →₀ ℕ := Finsupp.single 0 d
  have hμdeg : μ.degree = d := Finsupp.degree_single 0 d
  have hμ3 : μ 3 = 0 := by simp [μ]
  have hme : μ.degree ≤ e := hμdeg ▸ he
  have hs := P3StandardMonomialWeightPolynomial.weight_sum_polynomial μ e hme hμ3
  rw [weight_eq μ e hme hμ3, hμdeg] at hs
  exact hs

end PaperP1.P3StandardMonomialParameters
