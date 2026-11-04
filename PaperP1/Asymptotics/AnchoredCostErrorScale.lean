module

public import PaperP1.Asymptotics.PowerGap
public import PaperP1.Asymptotics.LogarithmicWordPowers

/-! # All proved anchored-cost errors are uniformly below the N^(2-a) scale -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnchoredCostErrorScale

def errorExponent (a : ℝ) : ℝ := (1 / 10 - a) / 2

theorem errorExponent_pos {a : ℝ} (ha : a < 1 / 10) : 0 < errorExponent a := by
  unfold errorExponent
  linarith only [ha]

theorem uniform_errors (D a t : ℝ) (hD : 0 ≤ D) (ha : 0 < a) (ha1 : a < 1 / 10) (ht : 0 < t) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ K : ℕ, ((K + 1 : ℕ) : ℝ) ≤ D * Real.log N →
      (N : ℝ) ^ (9 / 10 + errorExponent a : ℝ) ≤ (t / 2) * N ∧
      (((K : ℝ) * (K + 1 : ℕ) + 1) + 1) * N +
          (N : ℝ) ^ (19 / 10 + errorExponent a : ℝ) +
          (N : ℝ) ^ (3 / 2 + errorExponent a : ℝ) ≤ t * (N : ℝ) ^ (2 - a) := by
  let ρ : ℝ := (1 - a) / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith only [ha1]
  obtain ⟨NP, hP⟩ := PaperP1.LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    D hD 4 2 ρ hρ
  obtain ⟨NV, hV⟩ := PowerGap.small (9 / 10 + errorExponent a) 1 (t / 2)
    (by unfold errorExponent; linarith only [ha]) (by positivity)
  obtain ⟨NE, hE⟩ := PowerGap.small (1 + ρ) (2 - a) (t / 3)
    (by dsimp [ρ]; linarith only [ha1]) (by positivity)
  obtain ⟨NR, hR⟩ := PowerGap.small (19 / 10 + errorExponent a) (2 - a) (t / 3)
    (by unfold errorExponent; linarith only [ha1]) (by positivity)
  obtain ⟨NH, hH⟩ := PowerGap.small (3 / 2 + errorExponent a) (2 - a) (t / 3)
    (by unfold errorExponent; linarith only [ha1]) (by positivity)
  refine ⟨max (max NP NV) (max (max NE NR) (max NH 2)), ?_⟩
  intro N hN K hK
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp := hP N (by omega) K hK
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * (K + 1 : ℝ) ^ 2)] at hp
  have hc : ((K : ℝ) * (K + 1 : ℕ) + 1) + 1 ≤ (N : ℝ) ^ ρ := by
    have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hpoly : ((K : ℝ) * (K + 1 : ℕ) + 1) + 1 ≤ 4 * (K + 1 : ℝ) ^ 2 := by
      push_cast
      nlinarith only [sq_nonneg (K : ℝ), hk]
    exact hpoly.trans hp
  have hend : (((K : ℝ) * (K + 1 : ℕ) + 1) + 1) * N ≤
      (t / 3) * (N : ℝ) ^ (2 - a) := by
    calc
      _ ≤ (N : ℝ) ^ ρ * N := mul_le_mul_of_nonneg_right hc hn.le
      _ = (N : ℝ) ^ (1 + ρ) := by
        conv_lhs => rhs; rw [← Real.rpow_one (N : ℝ)]
        rw [← Real.rpow_add hn]
        congr 1
        ring
      _ ≤ _ := hE N (by omega)
  refine ⟨by simpa only [Real.rpow_one] using hV N (by omega), ?_⟩
  have hr := hR N (by omega)
  have hh := hH N (by omega)
  linarith only [hend, hr, hh]

end PaperP1.AnchoredCostErrorScale
