module

public import PaperP1.Asymptotics.LowConnectedRankMass
public import PaperP1.Asymptotics.NearPrimitiveTripleMass
public import PaperP1.Asymptotics.StrongNonalignedTripleProfile
public import PaperP1.Model.TripleRankGeometry

/-! # A weak pair replaces the global nonaligned rank bound in a triple sector

The rank cutoff is chosen before the threshold. Every exact pair is weak,
and one weak pair caps the entire triple nullity at three halves of L.
No pointwise nonaligned rank theorem or growing-degree curve input is used.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeakPairTripleMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = 3 ∧ ConnectedWindowFamilies.Connected L I ∧
        (∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ ActualOffsetNonalignment.NoExact x y L →
          (FreeComponentRank.pairIntersectionRank x y L : ℝ) ≤ θ * ((L + 1 : ℕ) : ℝ)) ∧
        ∃ x ∈ I, ∃ y ∈ I, x ≠ y ∧
          (FreeComponentRank.pairIntersectionRank x y L : ℝ) ≤ θ * ((L + 1 : ℕ) : ℝ)) →
      (∑ I ∈ F, infiniteJointMoment L I) ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  classical
  obtain ⟨b, hb⟩ := exists_nat_gt (max 1 (4 / ε))
  have hbR : (0 : ℝ) < b := lt_trans (by norm_num) ((le_max_left _ _).trans_lt hb)
  have hbN : 0 < b := by exact_mod_cast hbR
  have hb1 : (1 : ℝ) < b := (le_max_left _ _).trans_lt hb
  have hprod : 4 < (b : ℝ) * ε := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hb)
  have hsmall : 1 / (b : ℝ) ≤ ε / 4 := (div_le_iff₀ hbR).mpr (by nlinarith only [hprod])
  let η : ℝ := 1 / (2 * b)
  let θ : ℝ := η / 200
  have hη : 0 < η := by dsimp [η]; positivity
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθsmall : θ < η / 100 := by dsimp [θ]; linarith only [hη]
  have hηsmall : η ≤ 1 := by
    dsimp [η]
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * b)).mpr (by linarith only [hb1])
  have hθhalf : θ ≤ 1 / 2 := by dsimp [θ]; linarith only [hηsmall]
  have hθquarter : θ ≤ 1 / 4 := by dsimp [θ]; linarith only [hηsmall]
  obtain ⟨NL, _hNL, hl⟩ := LowConnectedRankMass.uniform_bound 3 (by omega) b hbN C (ε / 4) (by positivity)
  obtain ⟨NW, _hNW, hw⟩ := NearPrimitiveTripleMass.uniform_mass
    C η θ (ε / 2) hη hθ.le hθsmall (by positivity)
  obtain ⟨NS, _hNS, hs⟩ := StrongNonalignedTripleProfile.main_12_2
    C θ (3 / 2) (ε / 2) hθ (by norm_num) (by positivity)
  rw [show min (3 / 2 : ℝ) (3 - 3 / 2) = 3 / 2 by norm_num] at hs
  rw [show -(3 / 2 : ℝ) = -3 / 2 by ring] at hs
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption 3 (-3 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨θ, hθ, 3 + NL + NW + NS + NG + NA, by omega, ?_⟩
  intro N hN L hband F hF
  have hL : 1 ≤ L := by have hh := hg N (by omega) L hband; omega
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let Low := fun I ↦ (runRelativeNullity L I : ℝ) < (L : ℝ) / b
  let Weak := fun I : Finset ℕ ↦ ∀ x ∈ I, ∀ y ∈ I, x ≠ y →
    (FreeComponentRank.pairIntersectionRank x y L : ℝ) ≤ θ * ((L + 1 : ℕ) : ℝ)
  let FL := F.filter Low
  let FW := F.filter fun I ↦ ¬ Low I ∧ Weak I
  let FS := F.filter fun I ↦ ¬ Weak I
  have hcover : F ⊆ (FL ∪ FW) ∪ FS := by
    intro I hI
    by_cases hlow : Low I
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hI, hlow⟩))
    · by_cases hweak : Weak I
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hI, hlow, hweak⟩))
      · exact mem_union_right _ (mem_filter.mpr ⟨hI, hweak⟩)
  have hlow : (∑ I ∈ FL, infiniteJointMoment L I) ≤ (N : ℝ) ^ (-3 / 2 + ε / 2) := by
    have hm := hl N (by omega) L hband FL (by
      intro I hI
      obtain ⟨hIF, hdim⟩ := mem_filter.mp hI
      exact ⟨(hF I hIF).1, (hF I hIF).2.1, (hF I hIF).2.2.1, hdim⟩)
    have hq : (∑ I ∈ FL, infiniteJointMoment L I) ≤ PrimitiveWindowMass.mass FL L :=
      sum_le_sum fun I _hI ↦ PrimitiveWindowMass.joint_le_weight L (by omega) I
    exact hq.trans (hm.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by
      norm_num only [Nat.cast_ofNat]
      linarith only [hsmall])))
  have hweak : (∑ I ∈ FW, infiniteJointMoment L I) ≤ (N : ℝ) ^ (-3 / 2 + ε / 2) := by
    have hm := hw N (by omega) L hband FW (by
      intro I hI
      obtain ⟨hIF, hnlow, hweak⟩ := mem_filter.mp hI
      have hdim : (L : ℝ) / b ≤ (runRelativeNullity L I : ℝ) := le_of_not_gt hnlow
      have hB : ((L + 1 : ℕ) : ℝ) ≤ 2 * L := by push_cast; linarith only [hLR]
      have he : η * ((L + 1 : ℕ) : ℝ) * b = ((L + 1 : ℕ) : ℝ) / 2 := by
        dsimp [η]
        field_simp
      have hηB : η * ((L + 1 : ℕ) : ℝ) ≤ (L : ℝ) / b :=
        (le_div_iff₀ hbR).mpr (by rw [he]; linarith only [hB])
      exact ⟨(hF I hIF).2.1, (hF I hIF).1, hηB.trans hdim, hweak⟩)
    have hq : (∑ I ∈ FW, infiniteJointMoment L I) ≤ PrimitiveWindowMass.mass FW L :=
      sum_le_sum fun I _hI ↦ PrimitiveWindowMass.joint_le_weight L (by omega) I
    exact hq.trans (hm.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hθhalf])))
  have hstrong : (∑ I ∈ FS, infiniteJointMoment L I) ≤ (N : ℝ) ^ (-3 / 2 + ε / 2) := by
    apply hs N (by omega) L hband FS
    intro I hI
    obtain ⟨hIF, hnweak⟩ := mem_filter.mp hI
    obtain ⟨hIG, hcard, hconn, hexact, hweakpair⟩ := hF I hIF
    change ¬ (∀ x ∈ I, ∀ y ∈ I, x ≠ y →
      (FreeComponentRank.pairIntersectionRank x y L : ℝ) ≤ θ * ((L + 1 : ℕ) : ℝ)) at hnweak
    push Not at hnweak
    obtain ⟨x, hx, y, hy, hxy, hbig⟩ := hnweak
    have hno : ActualOffsetNonalignment.NoExact x y L := by
      by_contra hbad
      exact (not_le_of_gt hbig) (hexact x hx y hy hxy hbad)
    have hLB : (L : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ L
    have hθLB := mul_le_mul_of_nonneg_left hLB hθ.le
    obtain ⟨u, hu, v, hv, huv, hweakuv⟩ := hweakpair
    have hpos (z : ℕ) (hz : z ∈ I) : 0 < z := by
      have hh := (mem_Ico.mp (hIG hz)).1
      omega
    have hρ := TripleRankGeometry.set_nullity_le_pair I hcard u v L hu hv huv hpos
    have hρR : (runRelativeNullity L I : ℝ) ≤ (L : ℝ) + FreeComponentRank.pairIntersectionRank u v L := by
      exact_mod_cast hρ
    have hB : ((L + 1 : ℕ) : ℝ) ≤ 2 * L := by push_cast; linarith only [hLR]
    have hθcap : θ * ((L + 1 : ℕ) : ℝ) ≤ (1 / 2 : ℝ) * L := by
      calc
        _ ≤ θ * (2 * L) := mul_le_mul_of_nonneg_left hB hθ.le
        _ ≤ (1 / 4 : ℝ) * (2 * L) := mul_le_mul_of_nonneg_right hθquarter (by positivity)
        _ = _ := by ring
    have hrank : (runRelativeNullity L I : ℝ) ≤ (3 / 2 : ℝ) * L := by
      linarith only [hρR, hweakuv, hθcap]
    exact ⟨hIG, hcard, hconn, hrank, x, hx, y, hy, hxy, hno, hθLB.trans hbig.le⟩
  have h0 := sum_le_sum_of_subset_of_nonneg hcover (fun I _ _ ↦ infiniteJointMoment_nonneg L I)
  have h1 := GraphStarWeights.sum_union_le_nonneg FL FW (infiniteJointMoment L) (infiniteJointMoment_nonneg L)
  have h2 := GraphStarWeights.sum_union_le_nonneg (FL ∪ FW) FS (infiniteJointMoment L) (infiniteJointMoment_nonneg L)
  have hfactor : 3 * (N : ℝ) ^ (-3 / 2 + ε / 2) ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
    convert ha N (by omega) using 1
    congr 1
    ring
  linarith only [h0, h1, h2, hlow, hweak, hstrong, hfactor]

end PaperP1.WeakPairTripleMass
