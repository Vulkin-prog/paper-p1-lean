module

public import PaperP1.Analysis.LocalAffineDerivativeFormula
public import Mathlib.Tactic.Linarith

/-! # Constructing an admissible short affine segment through an interior point -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShortCenteredAffineSegment

open Set LocalAffineDerivativeFormula

theorem exists_segment (l v a b x₀ : ℝ) (hx : x₀ ∈ Ioo l v) (hx' : x₀ ∈ Ioo a b) (r : ℕ) :
    ∃ δ u c : ℝ, 0 < δ ∧ 0 < c ∧ c ≤ 1 ∧
      c ≤ δ / (2 * ((r + 1 : ℕ) : ℝ)) ∧
      parameter u c (1 / 2) = x₀ ∧ x₀ ∈ Ioo u (u + c) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1,
        (l + δ ≤ parameter u c t ∧ parameter u c t ≤ v - δ) ∧ parameter u c t ∈ Ioo a b := by
  let ε := min (min (x₀ - l) (v - x₀)) (min (x₀ - a) (b - x₀))
  have hε : 0 < ε := lt_min (lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2))
    (lt_min (sub_pos.mpr hx'.1) (sub_pos.mpr hx'.2))
  have hεl : ε ≤ x₀ - l := (min_le_left _ _).trans (min_le_left _ _)
  have hεv : ε ≤ v - x₀ := (min_le_left _ _).trans (min_le_right _ _)
  have hεa : ε ≤ x₀ - a := (min_le_right _ _).trans (min_le_left _ _)
  have hεb : ε ≤ b - x₀ := (min_le_right _ _).trans (min_le_right _ _)
  let δ := ε / 4
  have hδ : 0 < δ := by positivity
  have hεδ : ε = 4 * δ := by dsimp only [δ]; ring
  have hR : (0 : ℝ) < 2 * ((r + 1 : ℕ) : ℝ) := by positivity
  let c := min (1 : ℝ) (δ / (2 * ((r + 1 : ℕ) : ℝ)))
  have hc : 0 < c := lt_min zero_lt_one (div_pos hδ hR)
  have hcone : c ≤ 1 := min_le_left _ _
  have hscale : c ≤ δ / (2 * ((r + 1 : ℕ) : ℝ)) := min_le_right _ _
  have hRle : (2 : ℝ) ≤ 2 * ((r + 1 : ℕ) : ℝ) := by
    have hn : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ r + 1 by omega)
    linarith
  have hmul : c * (2 * ((r + 1 : ℕ) : ℝ)) ≤ δ := (le_div_iff₀ hR).mp hscale
  have htwo : 2 * c ≤ δ := by
    have hm := mul_le_mul_of_nonneg_left hRle hc.le
    nlinarith
  let u := x₀ - c / 2
  refine ⟨δ, u, c, hδ, hc, hcone, hscale, ?_, ?_, ?_⟩
  · dsimp only [parameter, u]
    ring
  · constructor <;> dsimp only [u] <;> linarith
  · intro t ht
    have hct : 0 < c * t := mul_pos hc ht.1
    have hctc : c * t < c := by simpa only [mul_one] using mul_lt_mul_of_pos_left ht.2 hc
    dsimp only [parameter, u]
    constructor <;> constructor <;> nlinarith

end PaperP1.ShortCenteredAffineSegment
