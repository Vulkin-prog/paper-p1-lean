module

public import PaperP1.Arithmetic.OrdinaryCandidateMonotonicity
public import PaperP1.Arithmetic.PrimeLogBudget

/-! # An explicit ordinary short-interval input and its two-candidate consequence

RelativeDensityInput is an independent analytic statement, not a theorem.
The passage from relative almost-all counts with positive density to two
ordinary smooth candidates is proved, including all finite initial losses.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryShortIntervalCensusInput

open Finset Filter PaperP1.NonanchorPivotSelection

local instance ordinaryCensusInputDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def relativeBad (ψ : ℕ → ℕ) (a ρ δ : ℝ) (X : ℕ) : Finset ℕ :=
  (range X).filter fun j ↦ δ * ψ j <
    |((ordinaryIndices j (ψ j + 1) ((j : ℝ) ^ (a / 2))).card : ℝ) - ρ * ψ j|

def prefixBad (ψ : ℕ → ℕ) (a : ℝ) (X : ℕ) : Finset ℕ :=
  (range X).filter fun j ↦ (ordinaryIndices j (ψ j + 1) ((j : ℝ) ^ (a / 2))).card < 2

def RelativeDensityInput (ψ : ℕ → ℕ) (a ρ : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ X₀ : ℕ, ∀ X ≥ X₀, ((relativeBad ψ a ρ δ X).card : ℝ) ≤ δ * X

def TwoCandidateDensity (ψ : ℕ → ℕ) (a : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ X₀ : ℕ, ∀ X ≥ X₀, ((prefixBad ψ a X).card : ℝ) ≤ τ * X

theorem two_candidates_of_relative (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop)
    (a ρ : ℝ) (hρ : 0 < ρ) (hInput : RelativeDensityInput ψ a ρ) : TwoCandidateDensity ψ a := by
  intro τ hτ
  let δ : ℝ := min (ρ / 2) (τ / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδρ : δ ≤ ρ / 2 := min_le_left _ _
  have hδτ : δ ≤ τ / 2 := min_le_right _ _
  obtain ⟨NE, hE⟩ := hInput δ hδ
  have hψReal := (tendsto_natCast_atTop_atTop (R := ℝ)).comp hψ
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hψReal.eventually (eventually_ge_atTop (4 / ρ)))
  obtain ⟨NX, hX⟩ := eventually_atTop.mp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (2 * (T : ℝ) / τ)))
  refine ⟨max NE NX, ?_⟩
  intro X hNX
  have hs : prefixBad ψ a X ⊆ range T ∪ relativeBad ψ a ρ δ X := by
    intro j hj
    obtain ⟨hjX, hjc⟩ := mem_filter.mp hj
    by_cases hjT : j < T
    · exact mem_union_left _ (mem_range.mpr hjT)
    · apply mem_union_right
      refine mem_filter.mpr ⟨hjX, ?_⟩
      have hlarge := hT j (by omega)
      change 4 / ρ ≤ (ψ j : ℝ) at hlarge
      have hprod : 4 ≤ ρ * (ψ j : ℝ) := by
        have h := (div_le_iff₀ hρ).mp hlarge
        nlinarith only [h]
      have hcard : ((ordinaryIndices j (ψ j + 1) ((j : ℝ) ^ (a / 2))).card : ℝ) ≤ 1 := by
        exact_mod_cast (show (ordinaryIndices j (ψ j + 1) ((j : ℝ) ^ (a / 2))).card ≤ 1 by omega)
      have hm := mul_le_mul_of_nonneg_right hδρ (Nat.cast_nonneg (ψ j))
      have hn := neg_le_abs (((ordinaryIndices j (ψ j + 1) ((j : ℝ) ^ (a / 2))).card : ℝ) - ρ * ψ j)
      nlinarith only [hprod, hcard, hm, hn]
  have hcNat := (card_le_card hs).trans (card_union_le _ _)
  rw [card_range] at hcNat
  have hc : ((prefixBad ψ a X).card : ℝ) ≤ (T : ℝ) + (relativeBad ψ a ρ δ X).card := by
    exact_mod_cast hcNat
  have he := hE X (by omega)
  have hx := (div_le_iff₀ hτ).mp (hX X (by omega))
  have hm := mul_le_mul_of_nonneg_right hδτ (Nat.cast_nonneg X)
  linarith only [hc, he, hx, hm]

end PaperP1.OrdinaryShortIntervalCensusInput
