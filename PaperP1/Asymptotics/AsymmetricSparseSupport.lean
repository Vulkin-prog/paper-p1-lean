module

public import PaperP1.Arithmetic.AsymmetricSupportEnvelope
public import PaperP1.Asymptotics.TruncatedAsymmetricSupportCount

/-! # Unconditional support of the literal asymmetric even-loss profile

For every old set in the permitted fixed-width interval, the number of
dyadic pairs with positive loss is N^(4/3+epsilon). This is a coarser
SUPPORT bound; no weighted31/24 profile or dense-sector estimate is claimed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AsymmetricSparseSupport

open PaperP1.Model

theorem uniform_count (C ε : ℝ) (Dold Dcut : ℕ) (hDold : 1 ≤ Dold) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (2 * Dold + 1) * (L + 1) ≤ H → H ≤ Dcut * (L + 1) →
      ∀ old : ℕ → Finset ℕ,
      (∀ x ∈ dyadicBlock N, ∀ n ∈ old x, |(n : ℤ) - x| ≤ ((Dold * (L + 1) : ℕ) : ℤ)) →
      ((AsymmetricSupportEnvelope.population N L H old).card : ℝ) ≤ (N : ℝ) ^ (4 / 3 + ε) := by
  obtain ⟨Nc, _hNc, hc⟩ := TruncatedAsymmetricSupportCount.uniform_count
    ((Dcut : ℝ) * CriticalBandScale.upperScale) ε
    (mul_nonneg (Nat.cast_nonneg _) CriticalBandScale.upperScale_pos.le) hε
  obtain ⟨Ns, hs⟩ := CriticalBandScale.critical_band_scale C
  obtain ⟨Nw, hw⟩ := CriticalPolynomialScale.polynomial_lt_scale C (Dcut : ℝ) (Nat.cast_nonneg _) 1
  refine ⟨max 4 (max Nc (max Ns Nw)), by omega, ?_⟩
  intro N hN L H hcrit hHlow hHhigh old hold
  let R := Dold * (L + 1)
  have hR : L + 1 ≤ R := by simpa only [one_mul] using Nat.mul_le_mul_right (L + 1) hDold
  have hH : 2 * R + 1 ≤ H := by dsimp [R]; nlinarith only [hHlow]
  have hHN : H ≤ N := by
    have hh := hw N (by omega) L hcrit
    simp only [pow_one] at hh
    have hh' : Dcut * (L + 1) < N := by exact_mod_cast hh
    omega
  have hlog : (H : ℝ) ≤ ((Dcut : ℝ) * CriticalBandScale.upperScale) * Real.log N := by
    have hh : (H : ℝ) ≤ (Dcut : ℝ) * ((L + 1 : ℕ) : ℝ) := by exact_mod_cast hHhigh
    have hb := mul_le_mul_of_nonneg_left (hs N (by omega) L hcrit).2 (Nat.cast_nonneg Dcut)
    nlinarith only [hh, hb]
  have hcard : ((AsymmetricSupportEnvelope.population N L H old).card : ℝ) ≤
      (TruncatedAsymmetricSupport.population N H (N - R + 1)).card := by
    exact_mod_cast AsymmetricSupportEnvelope.population_card old hR hH hHN hold
  exact hcard.trans (hc N (by omega) H (N - R + 1) (by omega) hHN (by omega) (by omega) (by omega) hlog)

end PaperP1.AsymmetricSparseSupport
