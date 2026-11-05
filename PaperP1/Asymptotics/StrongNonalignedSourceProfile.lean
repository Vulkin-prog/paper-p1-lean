module

public import PaperP1.Asymptotics.StrongNoExactPairMass
public import PaperP1.Asymptotics.LowCrossingTargetJointMass
public import PaperP1.Asymptotics.DenseOneTargetTripleJointMass

/-! # The complete true conditional profile above strongly intersecting nonaligned pairs

All low and dense target counts and the actual source-pair count are internally proved.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.StrongNonalignedSourceProfile

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_sources
    (C θ σ ε : ℝ) (hθ : 0 < θ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ P : Finset (ℕ × ℕ),
      (∀ p ∈ P, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N ∧ p.1 ≠ p.2 ∧
        ActualOffsetNonalignment.NoExact p.1 p.2 L ∧
        θ * L ≤ (FreeComponentRank.pairIntersectionRank p.1 p.2 L : ℝ)) →
      ∀ S : (ℕ × ℕ) → Finset ℕ,
      (∀ p ∈ P, ∀ z ∈ S p, z ∈ dyadicBlock N ∧ z ∉ ({p.1, p.2} : Finset ℕ) ∧
        ConnectedWindowFamilies.Connected L (insert z {p.1, p.2}) ∧
        (runRelativeNullity L (insert z {p.1, p.2}) : ℝ) ≤ σ * L) →
      (∑ p ∈ P, ∑ z ∈ S p, infiniteJointMoment L (insert z {p.1, p.2})) ≤
        (N : ℝ) ^ (-min (3 / 2) (3 - σ) + ε) := by
  classical
  let δ := ε / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨b, hb⟩ := exists_nat_gt (max 1 (8 / ε))
  have hbR : (0 : ℝ) < b := lt_trans (by norm_num) ((le_max_left _ _).trans_lt hb)
  have hbN : 0 < b := by exact_mod_cast hbR
  have hprod : 8 < (b : ℝ) * ε := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hb)
  have hsmall : 1 / (b : ℝ) ≤ ε / 8 := (div_le_iff₀ hbR).mpr (by nlinarith only [hprod])
  obtain ⟨NC, _hNC, hpc⟩ := StrongNoExactPairMass.uniform_count C θ δ hθ hδ
  obtain ⟨NQ, _hNQ, hq⟩ := StrongNoExactPairMass.uniform_joint_sum C θ δ hθ hδ
  obtain ⟨NL, _hNL, hl⟩ := LowCrossingTargetJointMass.uniform_bound 2 b hbN C δ hδ
  obtain ⟨ND, _hND, hd⟩ := DenseOneTargetTripleJointMass.uniform_bound C (1 / (b : ℝ)) σ δ
    (by positivity) hσ.le hδ
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption 2
    (-min (3 / 2) (3 - σ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨3 + NC + NQ + NL + ND + NA, by omega, ?_⟩
  intro N hN L hband P hP S hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpdata (p : ℕ × ℕ) (hp : p ∈ P) :
      p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N ∧ ActualOffsetNonalignment.NoExact p.1 p.2 L ∧
        θ * L ≤ (FreeComponentRank.pairIntersectionRank p.1 p.2 L : ℝ) :=
    ⟨(hP p hp).1, (hP p hp).2.1, (hP p hp).2.2.2.1, (hP p hp).2.2.2.2⟩
  have hcount := hpc N (by omega) L hband P hpdata
  have hpairmass := hq N (by omega) L hband P hpdata
  let Q := fun (p : ℕ × ℕ) (z : ℕ) ↦ (1 / (b : ℝ)) * L ≤ (OneTargetCrossing.rank {p.1, p.2} L z : ℝ)
  let SL := fun p ↦ (S p).filter fun z ↦ ¬Q p z
  let SD := fun p ↦ (S p).filter (Q p)
  have heG (p : ℕ × ℕ) (hp : p ∈ P) : ({p.1, p.2} : Finset ℕ) ⊆ dyadicBlock N := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact (hP p hp).1
    · exact mem_singleton.mp hx ▸ (hP p hp).2.1
  have hlowp (p : ℕ × ℕ) (hp : p ∈ P) :
      (∑ z ∈ SL p, infiniteJointMoment L (insert z {p.1, p.2})) ≤
        infiniteJointMoment L {p.1, p.2} * (N : ℝ) ^ (-(1 : ℝ) / 2 + 1 / (b : ℝ) + δ) := by
    apply hl N (by omega) L hband {p.1, p.2} (card_pair (hP p hp).2.2.1) (heG p hp) (SL p)
      (fun z hz ↦ (hS p hp z (mem_filter.mp hz).1).1)
    intro z hz
    obtain ⟨hzS, hnQ⟩ := mem_filter.mp hz
    obtain ⟨_hzG, hfresh, hconn, _hrank⟩ := hS p hp z hzS
    refine ⟨hfresh, OneTargetCrossing.connected_positive _ L z (by simp) hfresh hconn, ?_⟩
    have hh : (OneTargetCrossing.rank {p.1, p.2} L z : ℝ) < (1 / (b : ℝ)) * L := lt_of_not_ge hnQ
    have he : (1 / (b : ℝ)) * L = (L : ℝ) / b := by ring
    exact he ▸ hh
  have hdensep (p : ℕ × ℕ) (hp : p ∈ P) :
      (∑ z ∈ SD p, infiniteJointMoment L (insert z {p.1, p.2})) ≤ (N : ℝ) ^ (-3 + σ + δ) := by
    apply hd N (by omega) L hband {p.1, p.2} (card_pair (hP p hp).2.2.1) (heG p hp) (SD p)
      (fun z hz ↦ (hS p hp z (mem_filter.mp hz).1).1)
    intro z hz
    obtain ⟨hzS, hQ⟩ := mem_filter.mp hz
    exact ⟨(hS p hp z hzS).2.1, hQ, (hS p hp z hzS).2.2.2⟩
  have hlow : (∑ p ∈ P, ∑ z ∈ SL p, infiniteJointMoment L (insert z {p.1, p.2})) ≤
      (N : ℝ) ^ (-min (3 / 2) (3 - σ) + ε / 2) := by
    calc
      _ ≤ ∑ p ∈ P, infiniteJointMoment L {p.1, p.2} *
          (N : ℝ) ^ (-(1 : ℝ) / 2 + 1 / (b : ℝ) + δ) := sum_le_sum hlowp
      _ = (∑ p ∈ P, infiniteJointMoment L {p.1, p.2}) *
          (N : ℝ) ^ (-(1 : ℝ) / 2 + 1 / (b : ℝ) + δ) := by rw [sum_mul]
      _ ≤ (N : ℝ) ^ (-1 + δ) * (N : ℝ) ^ (-(1 : ℝ) / 2 + 1 / (b : ℝ) + δ) :=
        mul_le_mul_of_nonneg_right hpairmass (Real.rpow_nonneg hn.le _)
      _ = (N : ℝ) ^ (-(3 : ℝ) / 2 + 1 / (b : ℝ) + 2 * δ) := by
        rw [← Real.rpow_add hn]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by
        have hh := min_le_left (3 / 2 : ℝ) (3 - σ)
        dsimp [δ]
        linarith only [hh, hsmall, hε])
  have hdense : (∑ p ∈ P, ∑ z ∈ SD p, infiniteJointMoment L (insert z {p.1, p.2})) ≤
      (N : ℝ) ^ (-min (3 / 2) (3 - σ) + ε / 2) := by
    calc
      _ ≤ ∑ _p ∈ P, (N : ℝ) ^ (-3 + σ + δ) := sum_le_sum hdensep
      _ = (P.card : ℝ) * (N : ℝ) ^ (-3 + σ + δ) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) ^ δ * (N : ℝ) ^ (-3 + σ + δ) :=
        mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg hn.le _)
      _ = (N : ℝ) ^ (-3 + σ + 2 * δ) := by rw [← Real.rpow_add hn]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by
        have hh := min_le_right (3 / 2 : ℝ) (3 - σ)
        dsimp [δ]
        linarith only [hh, hε])
  have hsplit : (∑ p ∈ P, ∑ z ∈ S p, infiniteJointMoment L (insert z {p.1, p.2})) =
      (∑ p ∈ P, ∑ z ∈ SL p, infiniteJointMoment L (insert z {p.1, p.2})) +
        (∑ p ∈ P, ∑ z ∈ SD p, infiniteJointMoment L (insert z {p.1, p.2})) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro p _hp
    exact (sum_filter_add_sum_filter_not (S p) (Q p)
      (fun z ↦ infiniteJointMoment L (insert z {p.1, p.2}))).symm.trans (add_comm _ _)
  calc
    _ ≤ 2 * (N : ℝ) ^ (-min (3 / 2) (3 - σ) + ε / 2) := by rw [hsplit]; linarith only [hlow, hdense]
    _ ≤ (N : ℝ) ^ ((-min (3 / 2) (3 - σ) + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.StrongNonalignedSourceProfile
