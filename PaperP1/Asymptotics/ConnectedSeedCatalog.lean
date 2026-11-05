module

public import PaperP1.Model.ConnectedSeedCatalog
public import PaperP1.Asymptotics.FixedPrimitiveMass
public import PaperP1.Asymptotics.CoarseConnectedTripleMass
public import PaperP1.Asymptotics.DirectCrossingSeedFamilies
public import PaperP1.Asymptotics.LowTwoPairSeeds
public import PaperP1.Asymptotics.DensePairCrossingFamilies

/-! # The complete actual finite connected seed catalog has joint mass N⁻¹ -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedSeedCatalog

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies

theorem uniform_mass (R : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      (∑ D ∈ ConnectedSeedCatalog.families G L R, infiniteJointMoment L D) ≤
        (N : ℝ) ^ (-1 + ε) := by
  classical
  have hprim (i : Fin (R + 1)) := FixedPrimitiveMass.uniform_fixed
    (max 3 i.val) (le_max_left _ _) C (ε / 2) (by positivity)
  choose NP _hNP hp using hprim
  have hdirect (i : Fin (R + 1)) := DirectCrossingSeedFamilies.uniform_seeds
    (max 2 i.val) (le_max_left _ _) C (ε / 2) (by positivity)
  choose ND _hND hd using hdirect
  obtain ⟨NT, _hNT, ht⟩ := CoarseConnectedTripleMass.uniform_mass C (ε / 2) (by positivity)
  obtain ⟨NL, _hNL, hl⟩ := LowTwoPairSeeds.uniform_seeds (1 / 12) C (ε / 2)
    (by norm_num) (by positivity)
  obtain ⟨NDense, _hNDense, hdense⟩ := DensePairCrossingFamilies.uniform_seeds C (1 / 12) (ε / 2)
    (by norm_num) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  let K : ℝ := 2 * ((R + 1 : ℕ) : ℝ) + 3
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption K (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NG + NF + NT + NL + NDense + univ.sup NP + univ.sup ND, by omega, ?_⟩
  intro N hN L hband G hG
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpower : (N : ℝ) ^ (-5 / 3 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [])
  have hP (h : ℕ) (hh : h ∈ Icc 3 R) :
      (∑ D ∈ primitiveFamilies G L h, infiniteJointMoment L D) ≤ (N : ℝ) ^ (-1 + ε / 2) := by
    let i : Fin (R + 1) := ⟨h, by have h := (mem_Icc.mp hh).2; omega⟩
    have hiN : NP i ≤ univ.sup NP := le_sup (f := NP) (mem_univ i)
    have hmax : max 3 i.val = h := max_eq_right (mem_Icc.mp hh).1
    have hbound := hp i N (by omega) L hband (primitiveFamilies G L h) (by
      intro D hD
      obtain ⟨hDG, hprim⟩ := mem_filter.mp hD
      obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hDG
      exact ⟨hsub.trans hG, hcard.trans hmax.symm, hprim⟩)
    exact (sum_le_sum (fun D _ ↦ PrimitiveWindowMass.joint_le_weight L hL D)).trans hbound
  have hPSum : (∑ h ∈ Icc 3 R, ∑ D ∈ primitiveFamilies G L h, infiniteJointMoment L D) ≤
      ((R + 1 : ℕ) : ℝ) * (N : ℝ) ^ (-1 + ε / 2) := by
    calc
      _ ≤ ∑ _h ∈ Icc 3 R, (N : ℝ) ^ (-1 + ε / 2) := sum_le_sum hP
      _ = ((Icc 3 R).card : ℝ) * (N : ℝ) ^ (-1 + ε / 2) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (show (Icc 3 R).card ≤ R + 1 by rw [Nat.card_Icc]; omega))
        (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hDir (h : ℕ) (hh : h ∈ Icc 2 (R - 2)) :
      (∑ D ∈ DirectCrossingSeedFamilies.families G L h, infiniteJointMoment L D) ≤
        (N : ℝ) ^ (-1 + ε / 2) := by
    let i : Fin (R + 1) := ⟨h, by have h := (mem_Icc.mp hh).2; omega⟩
    have hiN : ND i ≤ univ.sup ND := le_sup (f := ND) (mem_univ i)
    have hmax : max 2 i.val = h := max_eq_right (mem_Icc.mp hh).1
    have hbound := hd i N (by omega) L hband G hG
    rw [hmax] at hbound
    exact hbound.trans hpower
  have hDirSum : (∑ h ∈ Icc 2 (R - 2), ∑ D ∈ DirectCrossingSeedFamilies.families G L h,
      infiniteJointMoment L D) ≤ ((R + 1 : ℕ) : ℝ) * (N : ℝ) ^ (-1 + ε / 2) := by
    calc
      _ ≤ ∑ _h ∈ Icc 2 (R - 2), (N : ℝ) ^ (-1 + ε / 2) := sum_le_sum hDir
      _ = ((Icc 2 (R - 2)).card : ℝ) * (N : ℝ) ^ (-1 + ε / 2) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by exact_mod_cast (show (Icc 2 (R - 2)).card ≤ R + 1 by rw [Nat.card_Icc]; omega))
        (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hT := ht N (by omega) L hband G hG (connectedFamilies G L 3) Subset.rfl
  have hLow := (hl N (by omega) L hband G hG).trans
    (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [] : (-4 / 3 : ℝ) + 1 / 12 + ε / 2 ≤ -1 + ε / 2))
  have hDense := (hdense N (by omega) L hband G hG).trans hpower
  have hfinite := ConnectedSeedCatalog.mass_bound G L R
  have hraw : (∑ D ∈ ConnectedSeedCatalog.families G L R, infiniteJointMoment L D) ≤
      K * (N : ℝ) ^ (-1 + ε / 2) := by
    dsimp [K]
    linarith only [hfinite, hPSum, hDirSum, hT, hLow, hDense]
  exact hraw.trans (by convert hf N (by omega) using 1; congr 1; ring)

end PaperP1.ConnectedSeedCatalog
