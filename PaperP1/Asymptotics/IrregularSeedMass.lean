module

public import PaperP1.Model.SingletonSeedMass
public import PaperP1.Model.RegularSetAsymptotic

/-! # The actual one-coordinate local-defect seed mass is N^(-1+epsilon) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IrregularSeedMass

open Finset PaperP1.Arithmetic PaperP1.RegularStarts PaperP1.RegularAffineBounds
  PaperP1.PrescribedTupleMass PaperP1.SingletonSeedMass PaperP1.Model

local instance irregularSeedMassTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem affine_sum (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, 0 < L →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ c : ℕ → Fin L → F₂,
        (∑ x ∈ irregularStarts N L, affineWindowMass x L (c x)) ≤
          (2 * (2 : ℝ) ^ C) * (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NR, hNR⟩ := RegularSetAsymptotic.dyadic_critical_relation_rank_le_one C
  obtain ⟨ND, hND⟩ := RegularSetAsymptotic.irregular_count_critical C ε hε
  refine ⟨max NR (max ND 2), ?_⟩
  intro N hN L hL hband c
  have hN2 : 2 ≤ N := by omega
  have hrel := hNR N (by omega) L hband
  have hcount := hND N (by omega) L hband
  have hfinite : (∑ x ∈ irregularStarts N L, affineWindowMass x L (c x)) ≤
      2 * (2 ^ L : ℝ)⁻¹ * ((irregularStarts N L).card : ℝ) := by
    calc
      _ ≤ ∑ _x ∈ irregularStarts N L, 2 * (2 ^ L : ℝ)⁻¹ := by
        apply sum_le_sum
        intro x hx
        have hxblock := ((mem_irregularStarts).mp hx).1
        have hxpos : 0 < x := by have h := (mem_Ico.mp hxblock).1; omega
        exact affineWindowMass_le_twice_nominal hxpos hL (hrel x hxblock) (c x)
      _ = _ := by simp [mul_comm]
  calc
    _ ≤ _ := hfinite
    _ ≤ 2 * ((2 ^ L : ℝ)⁻¹ * (N : ℝ) ^ ε) := by
      have h := mul_le_mul_of_nonneg_left hcount (by positivity : (0 : ℝ) ≤ 2 * (2 ^ L : ℝ)⁻¹)
      simpa only [mul_assoc] using h
    _ ≤ 2 * ((2 : ℝ) ^ C * (N : ℝ) ^ (-1 + ε)) :=
      mul_le_mul_of_nonneg_left (RegularSetAsymptotic.nominal_times_rpow_bound hN2 hband) (by norm_num)
    _ = _ := by ring

theorem seed_family (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, 0 < L →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ c : ℕ → Fin L → F₂,
        (∑ x ∈ seeds (irregularStarts N L), joint L c x) ≤
          (2 * (2 : ℝ) ^ C) * (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨N₀, hN₀⟩ := affine_sum C ε hε
  exact ⟨N₀, fun N hN L hL hband c ↦ by rw [sum_seeds]; exact hN₀ N hN L hL hband c⟩

theorem seed_coordinates (N L : ℕ) :
    ∀ x ∈ seeds (irregularStarts N L), ∀ i, x i ∈ Ico N (2 * N) :=
  seeds_coordinates _ _ (fun _ hx ↦ (mem_irregularStarts.mp hx).1)

end PaperP1.IrregularSeedMass
