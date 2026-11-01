module

public import PaperP1.Model.ContactPairMass
public import PaperP1.Asymptotics.ContactDefectBudget
public import PaperP1.Asymptotics.CriticalChannelPowers

/-! # Exact-contact pair seeds have total actual mass N^(-1+epsilon) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ContactSeedMass

open Finset PaperP1.Arithmetic PaperP1.PrescribedTupleMass PaperP1.ContactPairMass

theorem point_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ c : ℕ → Fin L → F₂,
      ∀ x ∈ Ico N (2 * N), joint L c (pair x (x + L)) ≤
        ((2 : ℝ) ^ C) ^ 2 * (N : ℝ) ^ (-2 + ε) := by
  obtain ⟨NP, hNP⟩ := ContactDefectBudget.relation_power C ε hε
  refine ⟨max NP 2, ?_⟩
  intro N hN L hband c x hx
  have hN2 : 2 ≤ N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hxpos : 0 < x := by have h := (mem_Ico.mp hx).1; omega
  have hpair := joint_le_relation_ratio c hxpos
  have hpow := hNP N (by omega) L hband x hx
  have hnominal := CriticalChannelPowers.nominal_square_upper hN2 hband
  have hden : (2 ^ (2 * L) : ℝ)⁻¹ = ((2 ^ L : ℝ)⁻¹) ^ 2 := by
    rw [show 2 * L = L * 2 by omega, pow_mul, inv_pow]
  rw [div_eq_mul_inv, hden] at hpair
  calc
    _ ≤ _ := hpair
    _ ≤ (N : ℝ) ^ ε * (((2 : ℝ) ^ C) ^ 2 * (N : ℝ) ^ (-2 : ℝ)) :=
      mul_le_mul hpow hnominal (by positivity) (Real.rpow_nonneg hNr.le _)
    _ = ((2 : ℝ) ^ C) ^ 2 * ((N : ℝ) ^ ε * (N : ℝ) ^ (-2 : ℝ)) := by ring
    _ = _ := by rw [← Real.rpow_add hNr, add_comm ε (-2 : ℝ)]

theorem forward_sum (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ c : ℕ → Fin L → F₂,
        (∑ x ∈ Ico N (2 * N), joint L c (pair x (x + L))) ≤
          ((2 : ℝ) ^ C) ^ 2 * (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NP, hNP⟩ := point_bound C ε hε
  refine ⟨max NP 1, ?_⟩
  intro N hN L hband c
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsize : (Ico N (2 * N)).card = N := by simp [two_mul]
  calc
    _ ≤ ∑ _x ∈ Ico N (2 * N), ((2 : ℝ) ^ C) ^ 2 * (N : ℝ) ^ (-2 + ε) :=
      sum_le_sum (fun x hx ↦ hNP N (by omega) L hband c x hx)
    _ = (N : ℝ) * (((2 : ℝ) ^ C) ^ 2 * (N : ℝ) ^ (-2 + ε)) := by
      rw [sum_const, nsmul_eq_mul, hsize]
    _ = ((2 : ℝ) ^ C) ^ 2 * ((N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-2 + ε)) := by rw [Real.rpow_one]; ring
    _ = _ := by rw [← Real.rpow_add hNr, show (1 : ℝ) + (-2 + ε) = -1 + ε by ring]

end PaperP1.ContactSeedMass
