module

public import PaperP1.Arithmetic.AlignedTargetCount
public import PaperP1.Asymptotics.CriticalBandScale
public import PaperP1.Asymptotics.LogarithmicWordPowers
public import PaperP1.Model.FiniteRademacher

/-! # All centers aligned with a fixed number of actual sources form a subpower pool

The fixed sources may overlap, be dependent, or have any actual local defects.
The finite polynomial count is uniform even in their numerical values.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AlignedSourcePool

open Finset PaperP1.Model PaperP1.CriticalBandScale

def pool {s : ℕ} (G : Finset ℕ) (x : Fin s → ℕ) (D L : ℕ) : Finset ℕ :=
  univ.biUnion fun i ↦ AlignedTargetCount.targets G D (x i) L

theorem mem_pool {s : ℕ} (G : Finset ℕ) (x : Fin s → ℕ) (D L z : ℕ) :
    z ∈ pool G x D L ↔ z ∈ G ∧ ∃ i : Fin s, CompressedTargetAlignment.Aligned D (x i) z L := by
  classical
  constructor
  · intro hz
    obtain ⟨i, _hi, hzi⟩ := mem_biUnion.mp hz
    exact ⟨(mem_filter.mp hzi).1, i, (mem_filter.mp hzi).2⟩
  · rintro ⟨hz, i, hi⟩
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr ⟨hz, hi⟩⟩

theorem card_bound {s : ℕ} (G : Finset ℕ) (x : Fin s → ℕ) (D L : ℕ) :
    (pool G x D L).card ≤ s * (4 * D + 1) * (L + 1) ^ 10 := by
  calc
    _ ≤ ∑ i : Fin s, (AlignedTargetCount.targets G D (x i) L).card := card_biUnion_le
    _ ≤ ∑ _i : Fin s, (4 * D + 1) * (L + 1) ^ 10 :=
      sum_le_sum fun i _ ↦ AlignedTargetCount.card_power_bound G D (x i) L
    _ = _ := by simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_assoc]

theorem uniform_count (s D : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x : Fin s → ℕ,
      ((pool (dyadicBlock N) x D L).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨NG, hg⟩ := critical_band_scale C
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le ((s * (4 * D + 1) : ℕ) : ℝ) 10 ε hε
  refine ⟨3 + NG + NP, by omega, ?_⟩
  intro N hN L hband x
  have hpoly := hp N (by omega) L (hg N (by omega) L hband).2
  calc
    _ ≤ ((s * (4 * D + 1) * (L + 1) ^ 10 : ℕ) : ℝ) := by
      exact_mod_cast card_bound (dyadicBlock N) x D L
    _ = ((s * (4 * D + 1) : ℕ) : ℝ) * (L + 1 : ℝ) ^ 10 := by
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    _ ≤ _ := (le_abs_self _).trans hpoly

end PaperP1.AlignedSourcePool
