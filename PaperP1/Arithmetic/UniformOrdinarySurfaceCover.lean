module

public import PaperP1.Geometry.OrdinarySurfaceCurveData
public import PaperP1.Arithmetic.OrdinaryIntegerPoints
public import PaperP1.Asymptotics.SurfaceCountParameters

/-! # The explicit uniform lifted-surface covering input on actual ordinary point sets

`UniformCover` records the actual ordinary point and curve property.
`UniformOrdinarySurfaceCoverFromExactSource.of_hypersurface_covers` derives it
from the exact P3 input using internally proved projection, curve, degree,
height, integer-point and uniform-constant transport. The primary covering
theorem, Salberger, arXiv:2311.05561v1, Lemma 2, remains unproved:
https://arxiv.org/pdf/2311.05561v1 . No unconditional covering theorem is asserted here.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformOrdinarySurfaceCover

open PaperP1.HomogeneousSplitRadicalRelations PaperP1.WeightedOrdinaryAffineIdeal
  PaperP1.OrdinarySurfaceCurveData PaperP1.OrdinaryIntegerPoints

def UniformCover (kmax K : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ (M : ℕ) (A : ℝ), 0 < A ∧
    ∀ k : ℕ, k ≤ kmax → ∀ (d : Fin k → ℤ) (I : Fin k → Finset ℤ) (j : Fin k → ℤ),
      (∀ i, d i ≠ 0) → (Pairwise fun i t ↦ Disjoint (I i) (I t)) → Function.Injective j →
      (∀ i, (I i).Nonempty) → (∀ i, (I i).card + 1 ≤ K) →
    let c : Fin k → ℚ := fun i ↦ (d i : ℚ)
    let J₀ : Fin k → Finset ℤ := fun i ↦ {j i}
    ∀ D : ℕ, 0 < D → ∀ H : ℕ, 1 ≤ H →
    ∀ U : Finset (Point (Fin k)), U ⊆ curvePoints (ordinaryIdeal c I J₀) H →
      ∃ (V : Finset (Point (Fin k))) (curves : Finset (Curve c D I J₀)),
        (∀ Γ ∈ curves, Γ.degree ≤ M) ∧
        (V.card : ℝ) ≤ A * (H : ℝ) ^ (2 / Real.sqrt ((2 : ℝ) ^ k) + δ) ∧
        (curves.card : ℝ) ≤ A * (H : ℝ) ^ (1 / Real.sqrt ((2 : ℝ) ^ k) + δ) ∧
        ∀ v ∈ U, v ∉ V → ∃ Γ ∈ curves, v ∈ curvePoints Γ.ideal H

theorem decay_mono {k l : ℕ} (h : k ≤ l) :
    1 / Real.sqrt ((2 : ℝ) ^ l) ≤ 1 / Real.sqrt ((2 : ℝ) ^ k) := by
  apply one_div_le_one_div_of_le (by positivity)
  exact Real.sqrt_le_sqrt (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h)

theorem subpower_parameters (q ε : ℝ) (hq : 0 ≤ q) (hε : 0 < ε) :
    ∃ (E k : ℕ) (δ : ℝ), 1 ≤ E ∧ 4 * (E + 1) ^ 2 ≤ k ∧ 0 < δ ∧
      ∀ l ≥ k, 2 * q / Real.sqrt ((2 : ℝ) ^ l) + q * δ ≤ ε / 2 ∧
        q / Real.sqrt ((2 : ℝ) ^ l) + q / ((E : ℝ) + 1) + 2 * q * δ ≤ ε / 2 := by
  obtain ⟨E, k, δ, hE, hk, hδ, hfirst, hsecond⟩ := SurfaceCountParameters.subpower_parameters q ε hq hε
  refine ⟨E, k, δ, hE, hk, hδ, ?_⟩
  intro l hl
  have hdecay : q / Real.sqrt ((2 : ℝ) ^ l) ≤ q / Real.sqrt ((2 : ℝ) ^ k) := by
    simpa only [one_div, div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left (decay_mono hl) hq
  constructor
  · have hf : 2 * (q / Real.sqrt ((2 : ℝ) ^ k)) + q * δ ≤ ε / 2 := by
      simpa only [mul_div_assoc] using hfirst
    have h : 2 * (q / Real.sqrt ((2 : ℝ) ^ l)) + q * δ ≤ ε / 2 := by linarith
    simpa only [mul_div_assoc] using h
  · nlinarith

end PaperP1.UniformOrdinarySurfaceCover
