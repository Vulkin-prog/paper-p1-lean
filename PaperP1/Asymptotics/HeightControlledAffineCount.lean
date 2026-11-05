module

public import PaperP1.Diophantine.GeometricAffinePointCount

/-! # The affine1/b count absorbs every fixed polynomial coefficient-height budget -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HeightControlledAffineCount

open Polynomial Finset BivariateDegrees BivariateHeight GeometricFactorSwap

theorem uniform_count (Amax Bmax κ : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ G : ℤ[X][X], degreeX G ≤ Amax → degreeY G ≤ Bmax →
      0 < degreeX G → 2 ≤ degreeY G → Geometric G → ∀ B : ℝ, 1 ≤ B →
      (height G : ℝ) ≤ C * B ^ κ → ∀ S : Finset (ℤ × ℤ),
      (∀ z ∈ S, G.evalEval z.1 z.2 = 0) →
      (∀ z ∈ S, |(z.1 : ℝ)| ≤ B) → (∀ z ∈ S, |(z.2 : ℝ)| ≤ B) →
        (S.card : ℝ) ≤ K * B ^ (1 / (degreeY G : ℝ) + ε) := by
  classical
  let θ := ε / ((κ : ℝ) + 1)
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  have hbudget : θ + (κ : ℝ) * θ = ε := by dsimp only [θ]; field_simp; ring
  choose K₀ hK₀ hcount using fun j : Fin (Amax + 1) × Fin (Bmax + 1) ↦
    GeometricAffinePointCount.finite_count (j.1.val + 1) (j.2.val + 2) (by omega) (by omega) θ hθ
  let Ksum : ℝ := ∑ j, K₀ j
  have hKsum : 0 ≤ Ksum := sum_nonneg (fun j _hj ↦ hK₀ j)
  let Cbase := max 1 C
  have hCb : 1 ≤ Cbase := le_max_left _ _
  let K := Ksum * Cbase ^ θ
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro G hGA hGB ha hb hgeo B hB hheight S hzero hx hy
  let j : Fin (Amax + 1) × Fin (Bmax + 1) :=
    (⟨degreeX G - 1, by omega⟩, ⟨degreeY G - 2, by omega⟩)
  have hja : j.1.val + 1 = degreeX G := by dsimp only [j]; omega
  have hjb : j.2.val + 2 = degreeY G := by dsimp only [j]; omega
  have hraw := hcount j G hja.symm hjb.symm hgeo B hB S hzero hx hy
  rw [hjb] at hraw
  have hKj : K₀ j ≤ Ksum := single_le_sum (fun i _hi ↦ hK₀ i) (mem_univ j)
  have hBp : 0 < B := by linarith
  have hheight' : (height G : ℝ) ≤ Cbase * B ^ κ :=
    hheight.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hBp.le _))
  have hheightθ : (height G : ℝ) ^ θ ≤ Cbase ^ θ * B ^ ((κ : ℝ) * θ) := by
    calc
      _ ≤ (Cbase * B ^ κ) ^ θ := Real.rpow_le_rpow (Nat.cast_nonneg _) hheight' hθ.le
      _ = Cbase ^ θ * (B ^ κ) ^ θ := Real.mul_rpow (by linarith) (pow_nonneg hBp.le _)
      _ = _ := by rw [← Real.rpow_natCast_mul hBp.le κ θ]
  calc
    (S.card : ℝ) ≤ K₀ j * B ^ (1 / (degreeY G : ℝ) + θ) * (height G : ℝ) ^ θ := hraw
    _ ≤ Ksum * B ^ (1 / (degreeY G : ℝ) + θ) * (Cbase ^ θ * B ^ ((κ : ℝ) * θ)) := by gcongr
    _ = (Ksum * Cbase ^ θ) * (B ^ (1 / (degreeY G : ℝ) + θ) * B ^ ((κ : ℝ) * θ)) := by ring
    _ = (Ksum * Cbase ^ θ) * B ^ ((1 / (degreeY G : ℝ) + θ) + (κ : ℝ) * θ) := by
      rw [← Real.rpow_add hBp]
    _ = K * B ^ (1 / (degreeY G : ℝ) + ε) := by
      have he : (1 / (degreeY G : ℝ) + θ) + (κ : ℝ) * θ = 1 / (degreeY G : ℝ) + ε := by linarith
      rw [he]

end PaperP1.HeightControlledAffineCount
