module

public import PaperP1.Model.WeakPairActivity
public import PaperP1.Asymptotics.DependentProductMass

/-! # Unconditional N^(-1+eta+epsilon) activity of actual weak/incompatible pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeakPairActivityAsymptotic

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

theorem critical_binary_power {N L : ℕ} {C : ℝ} (hN : 2 ≤ N)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) (η : ℝ) (hη : 0 ≤ η) :
    (2 : ℝ) ^ (η * L) ≤ (2 : ℝ) ^ (η * C) * (N : ℝ) ^ η := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hupper : (L : ℝ) ≤ Real.log N / Real.log 2 + C := by have h := (abs_le.mp hband).2; linarith
  have hm := mul_le_mul_of_nonneg_right hupper h2.le
  rw [add_mul, div_mul_cancel₀ _ h2.ne'] at hm
  have hs := mul_le_mul_of_nonneg_left hm hη
  simp only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [Real.rpow_def_of_pos hn, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hs]

theorem uniform_activity (C η ε : ℝ) (hη : 0 ≤ η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      CompatibleActivitySplit.absolute L (WeakPairActivity.pairs G L η) ≤
        (N : ℝ) ^ (-1 + η + ε) := by
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let D := 2 * (2 : ℝ) ^ (η * C)
  obtain ⟨NM, _hNM, hm⟩ := DependentProductMass.uniform_mass 2 C δ hδ
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption D (-1 + η + δ) δ hδ
  refine ⟨max 2 (max NM (max NG NF)), by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hpower := critical_binary_power (by omega) hband η hη
  calc
    _ ≤ (2 * (2 : ℝ) ^ (η * L)) * DependentProductMass.mass G L 2 :=
      WeakPairActivity.finite_bound G L hL η hη
    _ ≤ (2 * (2 : ℝ) ^ (η * L)) * (N : ℝ) ^ (-1 + δ) :=
      mul_le_mul_of_nonneg_left (hm N (by omega) L hband G hG) (by positivity)
    _ ≤ (2 * ((2 : ℝ) ^ (η * C) * (N : ℝ) ^ η)) * (N : ℝ) ^ (-1 + δ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpower (by norm_num)) (by positivity)
    _ = D * (N : ℝ) ^ (-1 + η + δ) := by
      rw [show -1 + η + δ = η + (-1 + δ) by ring, Real.rpow_add hn η (-1 + δ)]
      dsimp [D]
      ring
    _ ≤ (N : ℝ) ^ ((-1 + η + δ) + δ) := hf N (by omega)
    _ = _ := by congr 1; dsimp [δ]; ring

end PaperP1.WeakPairActivityAsymptotic
