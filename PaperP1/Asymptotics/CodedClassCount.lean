module

public import PaperP1.Asymptotics.ClassCodeBudget
public import PaperP1.Asymptotics.ClassCodeFibres

/-! # Unconditional count of the literal two-class target cover -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CodedClassCount

open Finset PaperP1.CodedClassTargets PaperP1.PhysicalClassData

theorem uniform_count (s K : ℕ) (C θ ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ a, x a ∈ Ico N (2 * N)) →
        ((targets x L (2 * (L + 1)) K N ⌊(N : ℝ) ^ θ⌋₊).card : ℝ) ≤
          (N : ℝ) ^ (2 * θ + ε) := by
  let δ := ε / 5
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨NP, hNP⟩ := ClassCodeBudget.position_count s K C δ hδ
  obtain ⟨NC, hNC⟩ := ClassCodeBudget.coefficient_count K C θ δ hδ
  obtain ⟨NF, hNF⟩ := ClassCodeFibres.pair_count s K C δ hδ
  obtain ⟨NG, hNG⟩ := CriticalWindowGeometry.uniform_geometry C 0
  refine ⟨max NP (max NC (max NF (max NG 3))), ?_⟩
  intro N hN L hband x hx
  have hN3 : 3 ≤ N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLN : L ≤ N := by have h := (hNG N (by omega) L hband).2.2.2.1; omega
  have hxpos : ∀ a, 2 ≤ x a := fun a ↦ by have h := (mem_Ico.mp (hx a)).1; omega
  have hcoeff (D : Finset (Option (Fin s) × Fin (L + 1))) (hD : D ∈ pool s L K) :
      ((ClassCoefficientValues.values (2 * (L + 1)) (sourceProduct x D) ⌊(N : ℝ) ^ θ⌋₊).card : ℝ) ≤
        (N : ℝ) ^ (θ + δ) :=
    hNC N (by omega) L hband _ (sourceProduct_le x hN3 hLN hx D ((mem_pool D).mp hD))
  have hfibre (a : Record s L) (ha : a ∈ equations x L (2 * (L + 1)) K ⌊(N : ℝ) ^ θ⌋₊)
      (b : Record s L) (hb : b ∈ equations x L (2 * (L + 1)) K ⌊(N : ℝ) ^ θ⌋₊) :
      ((pairSolutions N a b).card : ℝ) ≤ (N : ℝ) ^ δ := by
    obtain ⟨haC, haD⟩ := (mem_equations _ _ _ _ _ a).mp ha
    obtain ⟨hbC, hbD⟩ := (mem_equations _ _ _ _ _ b).mp hb
    exact hNF N (by omega) L hband a b ((mem_pool a.1).mp haC) ((mem_pool b.1).mp hbC)
      (ClassCoefficientValues.values_pos (sourceProduct_pos x hxpos a.1) haD)
      (ClassCoefficientValues.values_pos (sourceProduct_pos x hxpos b.1) hbD)
  have hfinite := targets_card x L (2 * (L + 1)) K N ⌊(N : ℝ) ^ θ⌋₊
    ((N : ℝ) ^ (θ + δ)) ((N : ℝ) ^ δ) (Real.rpow_nonneg hNr.le _) hcoeff hfibre
  have hpositions := hNP N (by omega) L hband
  calc
    _ ≤ _ := hfinite
    _ ≤ ((N : ℝ) ^ δ * (N : ℝ) ^ (θ + δ)) ^ 2 * (N : ℝ) ^ δ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hNr.le _)
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_mul_of_nonneg_right hpositions (Real.rpow_nonneg hNr.le _)
    _ = _ := by
      rw [← Real.rpow_add hNr, ← Real.rpow_natCast, ← Real.rpow_mul hNr.le, ← Real.rpow_add hNr]
      congr 1
      dsimp [δ]
      ring

end PaperP1.CodedClassCount
