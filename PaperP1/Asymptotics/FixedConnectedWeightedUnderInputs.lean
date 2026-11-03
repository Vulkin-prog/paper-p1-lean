module

public import PaperP1.Asymptotics.CoarseConnectedActivityUnderInputs

/-! # Actual bounded-order families with no singleton canonical components have total absolute centered activity N⁻¹ -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedConnectedWeightedUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CoarseConnectedParameters

theorem uniform_bound (R : ℕ) (v C ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε) :
    ∃ pc pi : Parameters R, ∃ pp : FinitePairDeficitInputs.Parameters,
      Hypotheses pc (ε / 32) → Hypotheses pi (ε / 128) →
      FinitePairDeficitInputs.Hypotheses pp (GeneralGraphHostCount.sizeCap (ε / 131072)) → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ G ∧ 3 ≤ I.card ∧ I.card ≤ R ∧
        ConnectedWindowFamilies.Connected L I) →
      (∑ I ∈ F, v ^ I.card * |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨pc, pi, pp, hp⟩ := CoarseConnectedActivityUnderInputs.uniform_range R C (ε / 2) (by positivity)
  let M := (max 1 v) ^ R
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (((R + 1 : ℕ) : ℝ) * M)
    (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨pc, pi, pp, ?_⟩
  intro hgeoC hgeoI hgeoP
  have hsC : (ε / 2) / 16 = ε / 32 := by ring
  have hsI : (ε / 2) / 64 = ε / 128 := by ring
  have hsP : (ε / 2) / 65536 = ε / 131072 := by ring
  obtain ⟨NJ, _hNJ, hj⟩ := hp (by simpa only [hsC] using hgeoC)
    (by simpa only [hsI] using hgeoI) (by simpa only [hsP] using hgeoP)
  refine ⟨10 + NJ + NF, by omega, ?_⟩
  intro N hN L hband G hG F hF
  have hsplit := sum_fiberwise_of_maps_to (s := F) (t := Icc 3 R) (g := fun I : Finset ℕ ↦ I.card)
    (fun I hI ↦ mem_Icc.mpr ⟨(hF I hI).2.1, (hF I hI).2.2.1⟩)
    (fun I ↦ v ^ I.card * |infiniteCenteredCoefficient L I|)
  have hcell (r : ℕ) (hr : r ∈ Icc 3 R) :
      (∑ I ∈ F.filter (fun I ↦ I.card = r), v ^ I.card * |infiniteCenteredCoefficient L I|) ≤
        M * (N : ℝ) ^ (-1 + ε / 2) := by
    have hmass := hj N (by omega) L hband r (mem_Icc.mp hr).1 (mem_Icc.mp hr).2 G hG
      (F.filter fun I ↦ I.card = r) (by
        intro I hI
        obtain ⟨hIF, hcard⟩ := mem_filter.mp hI
        exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨(hF I hIF).1, hcard⟩, (hF I hIF).2.2.2⟩)
    have hvpow : v ^ r ≤ M :=
      (pow_le_pow_left₀ hv (le_max_right 1 v) r).trans
        (pow_le_pow_right₀ (le_max_left 1 v) (mem_Icc.mp hr).2)
    calc
      _ = v ^ r * ∑ I ∈ F.filter (fun I ↦ I.card = r), |infiniteCenteredCoefficient L I| := by
        rw [mul_sum]
        exact sum_congr rfl (fun I hI ↦ by rw [(mem_filter.mp hI).2])
      _ ≤ v ^ r * (N : ℝ) ^ (-1 + ε / 2) := mul_le_mul_of_nonneg_left hmass (pow_nonneg hv r)
      _ ≤ _ := mul_le_mul_of_nonneg_right hvpow (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  calc
    _ = ∑ r ∈ Icc 3 R, ∑ I ∈ F.filter (fun I ↦ I.card = r), v ^ I.card * |infiniteCenteredCoefficient L I| := hsplit.symm
    _ ≤ ∑ _r ∈ Icc 3 R, M * (N : ℝ) ^ (-1 + ε / 2) := sum_le_sum hcell
    _ = ((Icc 3 R).card : ℝ) * (M * (N : ℝ) ^ (-1 + ε / 2)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ((R + 1 : ℕ) : ℝ) * (M * (N : ℝ) ^ (-1 + ε / 2)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (show (Icc 3 R).card ≤ R + 1 by rw [Nat.card_Icc]; omega))
        (mul_nonneg (by dsimp [M]; positivity) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
    _ = (((R + 1 : ℕ) : ℝ) * M) * (N : ℝ) ^ (-1 + ε / 2) := by ring
    _ ≤ _ := by
      convert hf N (by omega) using 1
      congr 1
      ring

end PaperP1.FixedConnectedWeightedUnderInputs
