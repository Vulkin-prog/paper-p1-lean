module

public import PaperP1.Model.NoSingletonSeedCover
public import PaperP1.Asymptotics.CoarseConnectedJointMassUnderInputs

/-! # Actual bounded-order families with no singleton canonical components have total joint mass N⁻¹ -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NoSingletonJointMassUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CoarseConnectedParameters

theorem uniform_range (R : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters R, Hypotheses p (ε / 4) → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ r : ℕ, 3 ≤ r → r ≤ R →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ G ∧ I.card = r ∧
        ∀ C ∈ ActualCanonicalComponents.blocks L I, 2 ≤ C.card) →
      (∑ I ∈ F, infiniteJointMoment L I) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨p, hp⟩ := CoarseConnectedJointMassUnderInputs.uniform_catalog_extensions R C ε hε
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨N₀, hN₀, h⟩ := hp hgeo
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband r hthree hcap G hG F hF
  apply h N hN L hband r hthree hcap G hG F
  intro I hI
  obtain ⟨hIG, hcard, hparts⟩ := hF I hI
  obtain ⟨D, hD, hDI⟩ := NoSingletonSeedCover.cover G L R I hIG (by omega) (by omega) hparts
  exact ⟨hIG, hcard, D, hD, hDI⟩

theorem uniform_weighted (R : ℕ) (v C ε : ℝ) (hv : 0 ≤ v) (hε : 0 < ε) :
    ∃ p : Parameters R, Hypotheses p (ε / 8) → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ G ∧ 3 ≤ I.card ∧ I.card ≤ R ∧
        ∀ C ∈ ActualCanonicalComponents.blocks L I, 2 ≤ C.card) →
      (∑ I ∈ F, v ^ I.card * infiniteJointMoment L I) ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨p, hp⟩ := uniform_range R C (ε / 2) (by positivity)
  let M := (max 1 v) ^ R
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (((R + 1 : ℕ) : ℝ) * M)
    (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  have hscale : (ε / 2) / 4 = ε / 8 := by ring
  obtain ⟨NJ, _hNJ, hj⟩ := hp (by simpa only [hscale] using hgeo)
  refine ⟨10 + NJ + NF, by omega, ?_⟩
  intro N hN L hband G hG F hF
  have hsplit := sum_fiberwise_of_maps_to (s := F) (t := Icc 3 R) (g := fun I : Finset ℕ ↦ I.card)
    (fun I hI ↦ mem_Icc.mpr ⟨(hF I hI).2.1, (hF I hI).2.2.1⟩)
    (fun I ↦ v ^ I.card * infiniteJointMoment L I)
  have hcell (r : ℕ) (hr : r ∈ Icc 3 R) :
      (∑ I ∈ F.filter (fun I ↦ I.card = r), v ^ I.card * infiniteJointMoment L I) ≤
        M * (N : ℝ) ^ (-1 + ε / 2) := by
    have hmass := hj N (by omega) L hband r (mem_Icc.mp hr).1 (mem_Icc.mp hr).2 G hG
      (F.filter fun I ↦ I.card = r) (by
        intro I hI
        obtain ⟨hIF, hcard⟩ := mem_filter.mp hI
        exact ⟨(hF I hIF).1, hcard, (hF I hIF).2.2.2⟩)
    have hvpow : v ^ r ≤ M :=
      (pow_le_pow_left₀ hv (le_max_right 1 v) r).trans
        (pow_le_pow_right₀ (le_max_left 1 v) (mem_Icc.mp hr).2)
    calc
      _ = v ^ r * ∑ I ∈ F.filter (fun I ↦ I.card = r), infiniteJointMoment L I := by
        rw [mul_sum]
        exact sum_congr rfl (fun I hI ↦ by rw [(mem_filter.mp hI).2])
      _ ≤ v ^ r * (N : ℝ) ^ (-1 + ε / 2) := mul_le_mul_of_nonneg_left hmass (pow_nonneg hv r)
      _ ≤ _ := mul_le_mul_of_nonneg_right hvpow (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  calc
    _ = ∑ r ∈ Icc 3 R, ∑ I ∈ F.filter (fun I ↦ I.card = r), v ^ I.card * infiniteJointMoment L I := hsplit.symm
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

end PaperP1.NoSingletonJointMassUnderInputs
