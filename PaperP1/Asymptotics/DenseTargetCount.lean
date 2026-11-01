module

public import PaperP1.Arithmetic.DenseTargetCover
public import PaperP1.Asymptotics.CodedClassCount
public import PaperP1.Arithmetic.UniformFixedSourceCertificates

/-! # Main Proposition 6.2: the actual uniform large-rank-loss target count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseTargetCount

open Finset Filter PaperP1.DenseTargetCover

theorem small_residual_exponent (s t : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, 1 ≤ k ∧ DenseTargetClassification.residualExponent s t k ≤ ε / 8 := by
  let R : ℝ := (((t - 1) * PhysicalLabelSupportCount.supportBound s t (t - 1) : ℕ) : ℝ)
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 (8 * R / ε))
  have hk1 : 1 ≤ k := by exact_mod_cast ((le_max_left _ _).trans_lt hk).le
  have hkr : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  refine ⟨k, hk1, ?_⟩
  change R / (k : ℝ) ≤ ε / 8
  apply (div_le_iff₀ hkr).mpr
  have h := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hk)
  nlinarith only [h]

/-- One threshold precedes every critical length and every actual source tuple.
Sources need not be distinct, separated, independent or locally regular. -/
theorem uniform_count (s : ℕ) (hs : 1 ≤ s) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ a, x a ∈ Ico N (2 * N)) →
        ((targets x L N η).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨t, _ht, hcover⟩ := DenseTargetCover.uniform_cover s hs η hη
  obtain ⟨k, hk, hθ⟩ := small_residual_exponent s t ε hε
  let θ := DenseTargetClassification.residualExponent s t k
  obtain ⟨L₀, hcover⟩ := hcover k hk
  obtain ⟨NS, hNS⟩ := UniformFixedSourceCertificates.companion_T4_2 s k hs hk C (ε / 2) (by positivity)
  obtain ⟨NC, hNC⟩ := CodedClassCount.uniform_count s (t - 1) C θ (ε / 4) (by positivity)
  obtain ⟨NG, hNG⟩ := CriticalWindowGeometry.uniform_geometry C (L₀ + 1)
  have hlarge : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (ε / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < ε / 2)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop 2)
  obtain ⟨NA, hNA⟩ := eventually_atTop.1 hlarge
  refine ⟨max NS (max NC (max NG (max NA 2))), ?_⟩
  intro N hN L hband x hx
  have hN2 : 2 ≤ N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL0 : L₀ ≤ L := by have h := (hNG N (by omega) L hband).2.1; omega
  have hcover := hcover N hN2 L hL0 x hx
  have hsource := hNS N (by omega) L hband x hx
  have hcode := hNC N (by omega) L hband x hx
  have hexponent : 2 * θ + ε / 4 ≤ ε / 2 := by dsimp [θ]; linarith only [hθ]
  have hcodeHalf := hcode.trans (Real.rpow_le_rpow_of_exponent_le hN1 hexponent)
  have hfinite : ((targets x L N η).card : ℝ) ≤
      (FixedSourceCertificate.sourceTargets x L k N).card +
        (CodedClassTargets.targets x L (2 * (L + 1)) (t - 1) N ⌊(N : ℝ) ^ θ⌋₊).card := by
    exact_mod_cast (card_le_card hcover).trans (card_union_le _ _)
  calc
    _ ≤ _ := hfinite
    _ ≤ 2 * (N : ℝ) ^ (ε / 2) := by linarith only [hsource, hcodeHalf]
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right (hNA N (by omega)) (Real.rpow_nonneg hNr.le _)
    _ = _ := by rw [← Real.rpow_add hNr]; congr 1; ring

def freshTargets {s : ℕ} (x : Fin s → ℕ) (L N : ℕ) (η : ℝ) : Finset ℕ :=
  targets x L N η \ univ.image x

theorem mem_freshTargets {s : ℕ} (x : Fin s → ℕ) (L N z : ℕ) (η : ℝ) :
    z ∈ freshTargets x L N η ↔ z ∈ Ico N (2 * N) ∧
      (∀ a, z ≠ x a) ∧ η * L ≤ (DenseTargetRegularization.loss (extended x z) L : ℝ) := by
  rw [freshTargets, Finset.mem_sdiff, DenseTargetCover.mem_targets]
  constructor
  · rintro ⟨⟨hz, hloss⟩, hnot⟩
    exact ⟨hz, fun a ha ↦ hnot (mem_image.mpr ⟨a, mem_univ _, ha.symm⟩), hloss⟩
  · rintro ⟨hz, hfresh, hloss⟩
    refine ⟨⟨hz, hloss⟩, ?_⟩
    intro hzimage
    obtain ⟨a, _, ha⟩ := mem_image.mp hzimage
    exact hfresh a ha.symm

/-- The literal source-excluding population in article Proposition 6.2. -/
theorem main_6_2 (s : ℕ) (hs : 1 ≤ s) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ a, x a ∈ Ico N (2 * N)) →
        ((freshTargets x L N η).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := uniform_count s hs C η ε hη hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband x hx
  exact (show ((freshTargets x L N η).card : ℝ) ≤ (targets x L N η).card from
    by exact_mod_cast card_le_card sdiff_subset).trans (hN₀ N hN L hband x hx)

end PaperP1.DenseTargetCount
