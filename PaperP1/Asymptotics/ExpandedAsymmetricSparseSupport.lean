module

public import PaperP1.Arithmetic.ExpandedAsymmetricSupportEnvelope
public import PaperP1.Asymptotics.ComparableTruncatedSupportCount
public import PaperP1.Asymptotics.AsymmetricSparseSupport

/-! # Unconditional asymmetric support on every fixed expanded dyadic range -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExpandedAsymmetricSparseSupport

open Finset PaperP1.ExpandedAsymmetricSupportEnvelope

theorem uniform_count (Q : ℕ) (hQ : 1 ≤ Q) (C ε : ℝ) (Dold Dcut : ℕ)
    (hDold : 1 ≤ Dold) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (2 * Dold + 1) * (L + 1) ≤ H → H ≤ Dcut * (L + 1) →
      ∀ old : ℕ → Finset ℕ,
      (∀ x ∈ block N Q, ∀ n ∈ old x, |(n : ℤ) - x| ≤ ((Dold * (L + 1) : ℕ) : ℤ)) →
      ((population N Q L H old).card : ℝ) ≤ (N : ℝ) ^ (4 / 3 + ε) := by
  let d := (Dcut : ℝ) * CriticalBandScale.upperScale
  have hd : 0 ≤ d := mul_nonneg (Nat.cast_nonneg _) CriticalBandScale.upperScale_pos.le
  obtain ⟨Nc, _hNc, hc⟩ := ComparableTruncatedSupportCount.uniform_count (2 * Q) d (ε / 2) hd (by positivity)
  obtain ⟨Ns, hs⟩ := CriticalBandScale.critical_band_scale C
  obtain ⟨Nw, hw⟩ := CriticalPolynomialScale.polynomial_lt_scale C (Dcut : ℝ) (Nat.cast_nonneg _) 1
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption
    ((Q : ℝ) ^ (4 / 3 + ε / 2)) (4 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 4 (max Nc (max Ns (max Nw Nf))), by omega, ?_⟩
  intro N hN L H hcrit hHlow hHhigh old hold
  let M := Q * N
  let R := Dold * (L + 1)
  let U := N - R + 1
  have hNM : N ≤ M := by simpa only [one_mul] using Nat.mul_le_mul_right N hQ
  have hR : L + 1 ≤ R := by simpa only [one_mul] using Nat.mul_le_mul_right (L + 1) hDold
  have hH : 2 * R + 1 ≤ H := by dsimp [R]; nlinarith only [hHlow]
  have hHN : H < N := by
    have hh := hw N (by omega) L hcrit
    simp only [pow_one] at hh
    have hh' : Dcut * (L + 1) < N := by exact_mod_cast hh
    omega
  have hRN : R < N := by omega
  have hhalf : N ≤ 2 * (U - 1) := by dsimp [U]; omega
  have hratio : M ≤ (2 * Q) * (U - 1) := by
    have hh := Nat.mul_le_mul_left Q hhalf
    dsimp [M]
    nlinarith only [hh]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : (H : ℝ) ≤ d * Real.log M := by
    have hHcast : (H : ℝ) ≤ (Dcut : ℝ) * ((L + 1 : ℕ) : ℝ) := by exact_mod_cast hHhigh
    have hb := mul_le_mul_of_nonneg_left (hs N (by omega) L hcrit).2 (Nat.cast_nonneg Dcut)
    have hbase : d * Real.log N ≤ d * Real.log M :=
      mul_le_mul_of_nonneg_left (Real.log_le_log hNpos (by exact_mod_cast hNM)) hd
    have hh : (H : ℝ) ≤ d * Real.log N := by dsimp [d]; nlinarith only [hHcast, hb]
    exact hh.trans hbase
  have hfinite : ((population N Q L H old).card : ℝ) ≤
      (TruncatedAsymmetricSupport.population M H U).card := by
    exact_mod_cast population_card old hRN hR hH hold
  calc
    _ ≤ ((TruncatedAsymmetricSupport.population M H U).card : ℝ) := hfinite
    _ ≤ (M : ℝ) ^ (4 / 3 + ε / 2) := hc M (by omega) H U (by omega) (by omega)
      (by dsimp [U]; omega) (by dsimp [U]; omega) hratio hlog
    _ = (Q : ℝ) ^ (4 / 3 + ε / 2) * (N : ℝ) ^ (4 / 3 + ε / 2) := by
      dsimp [M]
      rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    _ ≤ _ := by
      simpa only [show (4 / 3 + ε / 2) + ε / 2 = 4 / 3 + ε by ring] using hf N (by omega)

end PaperP1.ExpandedAsymmetricSparseSupport
