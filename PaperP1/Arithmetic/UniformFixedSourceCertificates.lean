module

public import PaperP1.Arithmetic.FixedSourceCertificate

/-! # Companion T4.2 uniformly over every fixed source tuple -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformFixedSourceCertificates

open Finset PaperP1.FixedSourceCertificate PaperP1.LogarithmicWordPowers
open PaperP1.CriticalBandScale

theorem logarithmic_width_le_nat_eventually (C : ℝ) (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ C * Real.log N → L ≤ N := by
  obtain ⟨N₀, hN₀⟩ := polynomial_factor_le_rpow_eventually C hC 1 1 1 (by norm_num)
  refine ⟨N₀, ?_⟩
  intro N hN L hL
  have h := hN₀ N hN L hL
  have hwidth : (L + 1 : ℝ) ≤ N := by
    simpa only [one_mul, pow_one, abs_of_nonneg (by positivity : (0 : ℝ) ≤ L + 1), Real.rpow_one] using h
  have hnat : L + 1 ≤ N := by exact_mod_cast hwidth
  omega

/-- The threshold precedes the length and every tuple of actual source centres. -/
theorem certificateTargets_le_power_eventually (s k : ℕ) (hk : 1 ≤ k)
    (C : ℝ) (hC : 0 ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ C * Real.log N →
      ∀ x : Fin s → ℕ, (∀ a, x a ∈ Finset.Ico N (2 * N)) →
        ((certificateTargets x L k N).card : ℝ) ≤ (N : ℝ) ^ ε := by
  let η : ℝ := ε / (2 * (k : ℝ))
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨Ndiv, hdiv⟩ := PaperP1.DivisorSubpolynomial.card_divisors_le_rpow_eventually 2 η hη
  obtain ⟨Npoly, hpoly⟩ := polynomial_factor_le_rpow_eventually C hC ((s : ℝ) ^ k) (2 * k)
    (ε / 2) (by linarith)
  obtain ⟨Nwidth, hwidth⟩ := logarithmic_width_le_nat_eventually C hC
  refine ⟨max Ndiv (max Npoly (max Nwidth 3)), ?_⟩
  intro N hN L hL x hx
  have hN3 : 3 ≤ N := by omega
  have hLN : L ≤ N := hwidth N (by omega) L hL
  have hdivSource (a : Fin s × Fin (L + 1)) :
      ((sourceValues x (L + 1) a).divisors.card : ℝ) ≤ (N : ℝ) ^ η :=
    hdiv N (by omega) _ (sourceValues_le_square x hN3 hLN hx a)
  have hfinite := finite_real_bound x L k N (by omega) ((N : ℝ) ^ η)
    (Real.rpow_nonneg (Nat.cast_nonneg N) _) hdivSource
  have hpolySource : (s : ℝ) ^ k * (L + 1 : ℝ) ^ (2 * k) ≤ (N : ℝ) ^ (ε / 2) := by
    simpa only [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (s : ℝ) ^ k * (L + 1 : ℝ) ^ (2 * k))]
      using hpoly N (by omega) L hL
  have hηmul : η * (k : ℝ) = ε / 2 := by
    dsimp [η]
    field_simp
  have hpower : ((N : ℝ) ^ η) ^ k = (N : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ η) k, ← Real.rpow_mul (Nat.cast_nonneg N), hηmul]
  calc
    _ ≤ (s : ℝ) ^ k * (L + 1 : ℝ) ^ (2 * k) * ((N : ℝ) ^ η) ^ k := hfinite
    _ ≤ (N : ℝ) ^ (ε / 2) * ((N : ℝ) ^ η) ^ k :=
      mul_le_mul_of_nonneg_right hpolySource (by positivity)
    _ = (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) := by rw [hpower]
    _ = _ := by
      rw [← Real.rpow_add (by exact_mod_cast (by omega : 0 < N) : (0 : ℝ) < N)]
      congr 1
      ring

theorem critical_band_certificateTargets (s k : ℕ) (hk : 1 ≤ k) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ a, x a ∈ Finset.Ico N (2 * N)) →
        ((certificateTargets x L k N).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨Nscale, hscale⟩ := critical_band_scale C
  obtain ⟨Ncount, hcount⟩ := certificateTargets_le_power_eventually s k hk upperScale upperScale_pos.le ε hε
  refine ⟨max Nscale Ncount, ?_⟩
  intro N hN L hL x hx
  exact hcount N (by omega) L (hscale N (by omega) L hL).2 x hx

/-- Original strict-product population, for every source tuple in the critical band. -/
theorem companion_T4_2 (s k : ℕ) (_hs : 1 ≤ s) (hk : 1 ≤ k) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ a, x a ∈ Finset.Ico N (2 * N)) →
        ((sourceTargets x L k N).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨Ncount, hcount⟩ := critical_band_certificateTargets s k hk C ε hε
  refine ⟨max Ncount 2, ?_⟩
  intro N hN L hL x hx
  have hsub : ((sourceTargets x L k N).card : ℝ) ≤ (certificateTargets x L k N).card := by
    exact_mod_cast card_le_card (sourceTargets_subset x L k N (by omega) hx)
  exact hsub.trans (hcount N (by omega) L hL x hx)

end PaperP1.UniformFixedSourceCertificates
