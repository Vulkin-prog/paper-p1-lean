module

public import PaperP1.Asymptotics.TwoSourceLatticeFamilies
public import PaperP1.Asymptotics.RoundedScaleLower

/-! # Both actual source lattices and sums at the literal rounded determinant scale -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RoundedSourceLatticeFamilies

open Finset PaperP1.DeterminantSourceBox PaperP1.DeterminantRelativeIntervals PaperP1.QuadraticIntervalGrid
open PaperP1.DeterminantHorizontalScale

theorem uniform_rounded_families (ε C ρ K A ζ : ℝ) (hε : 0 < ε) (hC : 0 < C) (hρ : 0 < ρ)
    (hζ : 0 < ζ) (hζsmall : ζ < 7 / 16) :
    ∃ κ₀ κ₁ N₀ : ℕ, ∀ N ≥ N₀, ∀ h : ℤ, h ≠ 0 → |(h : ℝ)| ≤ K * (Real.log N) ^ A →
      ∀ δ : ℝ, ∀ X : Box N ρ C δ,
      let M := horizontalScale N X.D X.E X.U X.V ζ
      32 ≤ M ∧ 2 * M ≤ N ∧ (M : ℝ) * |(h : ℝ)| ≤ N ∧
      ∃ A₀ B₀ A₁ B₁ : ℕ → Matrix (Fin 2) (Fin 2) ℤ, ∃ L₀ L₁ T₀ T₁ : ℕ → ℝ,
        (∀ k : ℕ, k ≤ 2 * M → HorizontalGridCoordinateData.Data X κ₀ M k (A₀ k) (B₀ k) (L₀ k) (L₁ k)) ∧
        (∀ q : ℕ, q ≤ 4 * M → VerticalGridCoordinateData.Data X κ₁ M q (A₁ q) (B₁ q) (T₀ q) (T₁ q)) ∧
        ∀ I : Finset ℕ, (∀ k ∈ I, M ≤ 4 * k) → (∀ k ∈ I, k ≤ 2 * M) →
          ((∑ k ∈ I, L₀ k) ≤ 60 * (N : ℝ) ^ ε * Real.sqrt (X.D * X.E * M) + 32 * X.E + 8 * X.D) ∧
          ((∑ k ∈ I, T₀ (grid M k)) ≤
            (512 * (2 * (49 + 16 / ρ)) * C / ρ) * (N : ℝ) ^ ε *
              (Real.sqrt (X.U * X.V * M) + X.U + X.V)) := by
  obtain ⟨κ₀, κ₁, NF, hfamilies⟩ := TwoSourceLatticeFamilies.uniform_two_families ε C ρ hε hC hρ
  obtain ⟨NL, hlower⟩ := RoundedScaleLower.uniform_lower 32 (by norm_num) ζ hζ
  obtain ⟨NA, hadmissible⟩ := DoubledDeterminantScale.uniform_doubled_admissible C ζ K A hC hζ.le hζsmall
  refine ⟨κ₀, κ₁, max 2 (max NF (max NL NA)), ?_⟩
  intro N hN h hh hshift δ X
  let M := horizontalScale N X.D X.E X.U X.V ζ
  have hM : 32 ≤ M := hlower N (by omega) X.D X.E X.U X.V
    X.D_ge_one X.E_ge_one X.U_ge_one X.V_ge_one
  have hc₁ : 0 < X.c₁ := by linarith [X.c₁_ge_one]
  have hc₂ : 0 < X.c₂ := by linarith [X.c₂_ge_one]
  have hD : 0 < X.D := by linarith [X.D_ge_one]
  have hE : 0 < X.E := by linarith [X.E_ge_one]
  have hU : 0 < X.U := by linarith [X.U_ge_one]
  have hV : 0 < X.V := by linarith [X.V_ge_one]
  have hcoeff : 1 ≤ X.c₁ * X.c₂ := by
    nlinarith [X.c₁_ge_one, X.c₂_ge_one,
      mul_nonneg (sub_nonneg.mpr X.c₁_ge_one) (sub_nonneg.mpr X.c₂_ge_one)]
  have hDE : 1 ≤ X.D * X.E := by
    nlinarith [X.D_ge_one, X.E_ge_one,
      mul_nonneg (sub_nonneg.mpr X.D_ge_one) (sub_nonneg.mpr X.E_ge_one)]
  have habs : (h.natAbs : ℝ) = |(h : ℝ)| := by
    have hz : (h.natAbs : ℤ) = |h| := Int.natCast_natAbs h
    simpa only [Int.cast_natCast, Int.cast_abs] using congrArg (fun z : ℤ ↦ (z : ℝ)) hz
  have hshift' : (h.natAbs : ℝ) ≤ K * (Real.log N) ^ A := by simpa only [habs] using hshift
  have had := hadmissible N (by omega) h.natAbs (Int.natAbs_pos.mpr hh) hshift'
    X.c₁ X.c₂ X.D X.E X.U X.V hc₁ hc₂ hD hE hU hV hcoeff hDE X.first_upper X.second_upper
  have hMh : (M : ℝ) * |(h : ℝ)| ≤ N := by
    rw [← habs]
    have hnonnegative : 0 ≤ (M : ℝ) * h.natAbs := by positivity
    nlinarith only [had.2.1, hnonnegative]
  refine ⟨hM, had.2.2, hMh, ?_⟩
  exact hfamilies N (by omega) M hM had.2.2 δ X

end PaperP1.RoundedSourceLatticeFamilies
