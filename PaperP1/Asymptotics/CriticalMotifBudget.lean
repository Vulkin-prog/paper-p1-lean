module

public import PaperP1.Arithmetic.SmoothMotifCodes
public import PaperP1.Arithmetic.LogarithmicPrimeCount
public import PaperP1.Asymptotics.CriticalWindowGeometry
public import Mathlib.Data.Fintype.Pi

/-! # A fixed triple of bounded motifs and small-prime codes has subpower many parameters -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalMotifBudget

open Finset PaperP1.TransverseMotifs PaperP1.SmoothMotifCodes PaperP1.CriticalBandScale

def motifPatterns (L d : ℕ) : Finset (Fin 3 → Finset (Vertex L)) :=
  Fintype.piFinset fun _ ↦ pool L d

def codePatterns (H : ℕ) : Finset (Fin 3 → Finset ℕ) := Fintype.piFinset fun _ ↦ codePool H

theorem motif_card (L d : ℕ) : (motifPatterns L d).card = (pool L d).card ^ 3 := by
  rw [motifPatterns, Fintype.card_piFinset_const]

theorem code_card (H : ℕ) : (codePatterns H).card = (codePool H).card ^ 3 := by
  rw [codePatterns, Fintype.card_piFinset_const]

theorem motif_polynomial_bound (L d : ℕ) :
    (motifPatterns L d).card ≤ ((d + 1) * 4 ^ d) ^ 3 * (L + 1) ^ (3 * d) := by
  have hB : 3 * (L + 1) + 1 ≤ 4 * (L + 1) := by omega
  have hh : (pool L d).card ≤ ((d + 1) * 4 ^ d) * (L + 1) ^ d := by
    calc
      _ ≤ (d + 1) * (3 * (L + 1) + 1) ^ d := card_pool L d
      _ ≤ (d + 1) * (4 * (L + 1)) ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hB d)
      _ = _ := by rw [mul_pow]; ring
  rw [motif_card]
  calc
    _ ≤ (((d + 1) * 4 ^ d) * (L + 1) ^ d) ^ 3 := Nat.pow_le_pow_left hh 3
    _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_comm d 3]

theorem uniform_motifs (C : ℝ) (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((motifPatterns L d).card : ℝ) ≤ (N : ℝ) ^ ε := by
  let A : ℕ := ((d + 1) * 4 ^ d) ^ 3
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le (A : ℝ) (3 * d) ε hε
  refine ⟨max 2 (max NG NP), by omega, ?_⟩
  intro N hN L hband
  have hB := (hg N (by omega) L hband).2.2.2.2.2
  have hpoly := hp N (by omega) L hB
  have hnonneg : 0 ≤ (A : ℝ) * (L + 1 : ℝ) ^ (3 * d) := by positivity
  rw [abs_of_nonneg hnonneg] at hpoly
  have hcard : ((motifPatterns L d).card : ℝ) ≤ (A : ℝ) * (L + 1 : ℝ) ^ (3 * d) := by
    dsimp only [A]
    exact_mod_cast motif_polynomial_bound L d
  exact hcard.trans hpoly

theorem uniform_codes (C : ℝ) (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ D * (L + 1) →
      ((codePatterns H).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨NP, hp⟩ := LogarithmicPrimeCount.smooth_support_count_le_rpow_eventually
    ((D : ℝ) * upperScale) (mul_nonneg (Nat.cast_nonneg D) upperScale_pos.le) (ε / 3) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 2 (max NP NG), by omega, ?_⟩
  intro N hN L H hband hcut
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hB := (hg N (by omega) L hband).2.2.2.2.2
  have hcutR : (H : ℝ) ≤ (D : ℝ) * ((L + 1 : ℕ) : ℝ) := by exact_mod_cast hcut
  have hlog : (H : ℝ) ≤ ((D : ℝ) * upperScale) * Real.log N := by
    have hh := mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg D)
    nlinarith only [hcutR, hh]
  have hs : ((codePool H).card : ℝ) ≤ (N : ℝ) ^ (ε / 3) := hp N (by omega) H hlog
  calc
    _ = ((codePool H).card : ℝ) ^ 3 := by rw [code_card, Nat.cast_pow]
    _ ≤ ((N : ℝ) ^ (ε / 3)) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hs 3
    _ = _ := by rw [pow_succ, pow_two, ← Real.rpow_add hn, ← Real.rpow_add hn]; congr 1; ring

theorem parameter_budget {α : Type*} [DecidableEq α] (C : ℝ) (D d k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → H ≤ D * (L + 1) →
      ∀ F : Finset α, F.card ≤ (L + 1) ^ k →
      ((((F ×ˢ motifPatterns L d) ×ˢ codePatterns H).card : ℕ) : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨NM, _hNM, hm⟩ := uniform_motifs C d (ε / 3) (by positivity)
  obtain ⟨NC, _hNC, hc⟩ := uniform_codes C D (ε / 3) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le 1 k (ε / 3) (by positivity)
  refine ⟨max 2 (max NM (max NC (max NG NP))), by omega, ?_⟩
  intro N hN L H hband hcut F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hB := (hg N (by omega) L hband).2.2.2.2.2
  have hpoly := hp N (by omega) L hB
  have hwidth : (L + 1 : ℝ) ^ k ≤ (N : ℝ) ^ (ε / 3) := by
    simpa only [one_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (L + 1 : ℝ) ^ k)] using hpoly
  have hF' : (F.card : ℝ) ≤ (N : ℝ) ^ (ε / 3) :=
    (show (F.card : ℝ) ≤ (L + 1 : ℝ) ^ k by exact_mod_cast hF).trans hwidth
  have hm' := hm N (by omega) L hband
  have hc' := hc N (by omega) L H hband hcut
  have htwo := mul_le_mul hF' hm' (Nat.cast_nonneg _) (Real.rpow_nonneg hn.le _)
  have hthree := mul_le_mul htwo hc' (Nat.cast_nonneg _)
    (mul_nonneg (Real.rpow_nonneg hn.le _) (Real.rpow_nonneg hn.le _))
  calc
    _ = (F.card : ℝ) * (motifPatterns L d).card * (codePatterns H).card := by
      rw [card_product, card_product, Nat.cast_mul, Nat.cast_mul]
    _ ≤ (N : ℝ) ^ (ε / 3) * (N : ℝ) ^ (ε / 3) * (N : ℝ) ^ (ε / 3) := hthree
    _ = _ := by rw [← Real.rpow_add hn, ← Real.rpow_add hn]; congr 1; ring

end PaperP1.CriticalMotifBudget
