module

public import PaperP1.Asymptotics.DeterminantHorizontalScale

/-! # The actual determinant scale remains admissible after doubling -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DoubledDeterminantScale

open PaperP1.DeterminantHorizontalScale PaperP1.DeterminantLogScale

theorem uniform_doubled_admissible (C ζ K A : ℝ) (hC : 0 < C) (hζ : 0 ≤ ζ) (hζsmall : ζ < 7 / 16) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ h : ℕ, 0 < h → (h : ℝ) ≤ K * (Real.log N) ^ A →
      ∀ c₁ c₂ D E U V : ℝ, 0 < c₁ → 0 < c₂ → 0 < D → 0 < E → 0 < U → 0 < V →
        1 ≤ c₁ * c₂ → 1 ≤ D * E → c₁ * D ^ 2 * U ≤ C * N → c₂ * E ^ 2 * V ≤ C * N →
          0 < horizontalScale N D E U V ζ ∧
            2 * (horizontalScale N D E U V ζ : ℝ) * h ≤ N ∧
              2 * horizontalScale N D E U V ζ ≤ N := by
  obtain ⟨N₀, hscale⟩ := uniform_admissible C ζ (2 * K) A hC hζ hζsmall
  refine ⟨N₀, ?_⟩
  intro N hN h hh hshift c₁ c₂ D E U V hc₁ hc₂ hD hE hU hV hcoeff hDE hfirst hsecond
  have hshift2 : ((2 * h : ℕ) : ℝ) ≤ (2 * K) * (Real.log N) ^ A := by
    push_cast
    nlinarith only [hshift]
  have hs := hscale N hN (2 * h) (by omega) hshift2 c₁ c₂ D E U V
    hc₁ hc₂ hD hE hU hV hcoeff hDE hfirst hsecond
  have hprod : 2 * (horizontalScale N D E U V ζ : ℝ) * h ≤ N := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm] using hs.2.1
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hsmall : 2 * (horizontalScale N D E U V ζ : ℝ) ≤ N := by
    have h := mul_nonneg (show 0 ≤ 2 * (horizontalScale N D E U V ζ : ℝ) by positivity) (sub_nonneg.mpr hhR)
    nlinarith
  exact ⟨hs.1, hprod, by exact_mod_cast hsmall⟩

end PaperP1.DoubledDeterminantScale
