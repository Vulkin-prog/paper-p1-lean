module

public import PaperP1.Asymptotics.AllCardinalityTotalActivityUnderInputs

/-! # All connected cardinalities below one actual rank plus two have total actual mass rate1 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedOneRankOffsetMassUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CoarseConnectedParameters
  PaperP1.ConnectedWindowFamilies

theorem uniform_bound (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ sl sj : ℕ, 1 ≤ sl ∧ 1 ≤ sj ∧ ∃ pc pi : Parameters sl,
      ∃ pp : FinitePairDeficitInputs.Parameters, ∃ pj : Parameters sj,
      Hypotheses pc (ε / 256) → Hypotheses pi (ε / 1024) →
      FinitePairDeficitInputs.Hypotheses pp (GeneralGraphHostCount.sizeCap (ε / 1048576)) →
      Hypotheses pj (ε / 64) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ G ∧ 3 ≤ I.card ∧ Connected L I ∧ runRelativeNullity L I ≤ L + 2) →
        (∑ I ∈ F, u ^ I.card * (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|)) ≤
          (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨sl, sj, hsl, hsj, pc, pi, pp, pj, hp⟩ := AllCardinalityTotalActivityUnderInputs.uniform_bound
    (1 + ε / 4) u C (ε / 2) (by positivity) hu (by positivity)
  obtain ⟨K, hK⟩ := exists_nat_ge (8 / ε)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C (K + 1)
  refine ⟨sl, sj, hsl, hsj, pc, pi, pp, pj, ?_⟩
  intro hgeoC hgeoI hgeoP hgeoJ
  have hsC : (ε / 2) / 128 = ε / 256 := by ring
  have hsI : (ε / 2) / 512 = ε / 1024 := by ring
  have hsP : (ε / 2) / 524288 = ε / 1048576 := by ring
  have hsJ : (ε / 2) / 32 = ε / 64 := by ring
  obtain ⟨NA, _hNA, ha⟩ := hp (by simpa only [hsC] using hgeoC)
    (by simpa only [hsI] using hgeoI) (by simpa only [hsP] using hgeoP) (by simpa only [hsJ] using hgeoJ)
  refine ⟨10 + NA + NG, by omega, ?_⟩
  intro N hN L hband G hG F hF
  have hlarge : 2 ≤ (ε / 4) * (L : ℝ) := by
    have hKL : K ≤ L := by have h := (hg N (by omega) L hband).2.1; omega
    have hL : 8 / ε ≤ (L : ℝ) := hK.trans (by exact_mod_cast hKL)
    have h := (div_le_iff₀ hε).mp hL
    nlinarith only [h]
  have h := ha N (by omega) L hband G hG F (by
    intro I hI
    obtain ⟨hIG, hthree, hconn, hcap⟩ := hF I hI
    have hcompatible := runCompatibleNullity_le_relative L I
    have hcapR : (runRelativeNullity L I : ℝ) ≤ (L : ℝ) + 2 := by exact_mod_cast hcap
    have hcR : (runCompatibleNullity L I : ℝ) ≤ runRelativeNullity L I := by exact_mod_cast hcompatible
    exact ⟨hIG, hthree, hconn, by nlinarith only [hcapR, hcR, hlarge]⟩)
  apply h.trans
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
  rw [min_eq_right (by linarith only [hε] : (2 : ℝ) - (1 + ε / 4) ≤ 1)]
  linarith only [hε]

end PaperP1.ConnectedOneRankOffsetMassUnderInputs
