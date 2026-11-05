module

public import PaperP1.Diophantine.GeometricBiformPointCount
public import PaperP1.Algebra.BivariateLargeRoot

/-! # Uniform biform counts absorb every fixed polynomial coefficient-height budget -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HeightControlledBiformCount

open Polynomial Finset PaperP1.BivariateDegrees PaperP1.BivariateHeight
open PaperP1.BidegreeOneFibreCount PaperP1.GeometricFactorSwap

theorem uniform_first_count (Amax Bmax κ : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ G : ℤ[X][X], degreeX G ≤ Amax → degreeY G ≤ Bmax →
      0 < degreeX G → 0 < degreeY G → Geometric G → ∀ L : ℝ, 1 ≤ L →
      (height G : ℝ) ≤ C * L ^ κ → ∀ S : Finset Point,
      (∀ z ∈ S, (z.1 0).natAbs.Coprime (z.1 1).natAbs ∧ (z.2 0).natAbs.Coprime (z.2 1).natAbs) →
      (∀ z ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1 (IntegerFactorProjectiveCurve.projective G) = 0) →
      (∀ z ∈ S, ∀ i, |(z.1 i : ℝ)| ≤ L) →
        (S.card : ℝ) ≤ K * L ^ (2 / (degreeY G : ℝ) + ε) := by
  classical
  let θ : ℝ := ε / ((κ : ℝ) + 1)
  have hκ : (0 : ℝ) < (κ : ℝ) + 1 := by positivity
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hbudget : θ + (κ : ℝ) * θ = ε := by dsimp [θ]; field_simp; ring
  choose K₀ hK₀ hcount using fun j : Fin (Amax + 1) × Fin (Bmax + 1) ↦
    GeometricBiformPointCount.full_input (j.1.val + 1) (j.2.val + 1) (by omega) (by omega) θ hθ
  let Ksum : ℝ := ∑ j, K₀ j
  have hKsum : 0 ≤ Ksum := Finset.sum_nonneg (fun j _ ↦ hK₀ j)
  let Cbase := max 1 C
  have hCb : 1 ≤ Cbase := le_max_left _ _
  let K := Ksum * Cbase ^ θ
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro G hGA hGB ha hb hgeo L hL hheight S hprim hzero hbox
  let j : Fin (Amax + 1) × Fin (Bmax + 1) :=
    (⟨degreeX G - 1, by omega⟩, ⟨degreeY G - 1, by omega⟩)
  have hja : j.1.val + 1 = degreeX G := by dsimp [j]; omega
  have hjb : j.2.val + 1 = degreeY G := by dsimp [j]; omega
  have hraw := hcount j G hja.symm hjb.symm hgeo L hL S hprim hzero hbox
  rw [hjb] at hraw
  have hKj : K₀ j ≤ Ksum := Finset.single_le_sum (fun i _ ↦ hK₀ i) (Finset.mem_univ j)
  have hL0 : 0 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hheight' : (height G : ℝ) ≤ Cbase * L ^ κ :=
    hheight.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hL0 _))
  have hheightθ : (height G : ℝ) ^ θ ≤ Cbase ^ θ * L ^ ((κ : ℝ) * θ) := by
    calc
      _ ≤ (Cbase * L ^ κ) ^ θ := Real.rpow_le_rpow (Nat.cast_nonneg _) hheight' hθ.le
      _ = Cbase ^ θ * (L ^ κ) ^ θ := Real.mul_rpow (by linarith) (pow_nonneg hL0 _)
      _ = _ := by rw [← Real.rpow_natCast_mul hL0 κ θ]
  calc
    (S.card : ℝ) ≤ K₀ j * L ^ (2 / (degreeY G : ℝ) + θ) * (height G : ℝ) ^ θ := hraw
    _ ≤ Ksum * L ^ (2 / (degreeY G : ℝ) + θ) * (Cbase ^ θ * L ^ ((κ : ℝ) * θ)) := by gcongr
    _ = (Ksum * Cbase ^ θ) * (L ^ (2 / (degreeY G : ℝ) + θ) * L ^ ((κ : ℝ) * θ)) := by ring
    _ = (Ksum * Cbase ^ θ) * L ^ ((2 / (degreeY G : ℝ) + θ) + (κ : ℝ) * θ) := by
      rw [← Real.rpow_add hLp]
    _ = K * L ^ (2 / (degreeY G : ℝ) + ε) := by
      have he : (2 / (degreeY G : ℝ) + θ) + (κ : ℝ) * θ = 2 / (degreeY G : ℝ) + ε := by linarith
      rw [he]

theorem uniform_second_count (Amax Bmax κ : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ G : ℤ[X][X], degreeX G ≤ Amax → degreeY G ≤ Bmax →
      0 < degreeX G → 0 < degreeY G → Geometric G → ∀ T : ℝ, 1 ≤ T →
      (height G : ℝ) ≤ C * T ^ κ → ∀ S : Finset Point,
      (∀ z ∈ S, (z.1 0).natAbs.Coprime (z.1 1).natAbs ∧ (z.2 0).natAbs.Coprime (z.2 1).natAbs) →
      (∀ z ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1 (IntegerFactorProjectiveCurve.projective G) = 0) →
      (∀ z ∈ S, ∀ i, |(z.2 i : ℝ)| ≤ T) →
        (S.card : ℝ) ≤ K * T ^ (2 / (degreeX G : ℝ) + ε) := by
  obtain ⟨K, hK, hcount⟩ := uniform_first_count Bmax Amax κ C ε hε
  refine ⟨K, hK, ?_⟩
  intro G hGA hGB ha hb hgeo T hT hheight S hprim hzero hbox
  have hc := hcount (Bivariate.swap G)
    (by simpa only [BivariateProjectiveSwap.degreeX_swap] using hGB)
    (by simpa only [BivariateProjectiveSwap.degreeY_swap] using hGA)
    (by simpa only [BivariateProjectiveSwap.degreeX_swap] using hb)
    (by simpa only [BivariateProjectiveSwap.degreeY_swap] using ha)
    (geometric_swap G hgeo) T hT (by simpa only [BivariateLargeRoot.height_swap] using hheight)
    (S.image Prod.swap)
    (by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
      exact ⟨(hprim w hw).2, (hprim w hw).1⟩)
    (by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
      exact (BivariateProjectiveSwap.evaluation_swap G w.1 w.2).trans (hzero w hw))
    (by
      intro z hz i
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
      exact hbox w hw i)
  simpa only [card_image_of_injective _ Prod.swap_injective, BivariateProjectiveSwap.degreeY_swap] using hc

end PaperP1.HeightControlledBiformCount
