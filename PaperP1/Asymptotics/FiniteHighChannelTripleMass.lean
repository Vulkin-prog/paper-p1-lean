module

public import PaperP1.Model.FiniteChannelTripleMass
public import PaperP1.Asymptotics.HomogeneousChannelMass
public import PaperP1.Asymptotics.UnorderedSeedMassPropagation

/-! # Triples containing a fixed good pair of height at least five have four-fifths mass

This consequence of T2.8 is unconditional: actual fixed-order seed
propagation and the homogeneous source upper bound suffice by themselves.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteHighChannelTripleMass

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FiniteChannelTripleMass
  PaperP1.GoodEdgePositivePalm PaperP1.GoodPairGeneratedTriples

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def channels (Q : ℕ) : Finset (ℕ × ℕ) := (FiniteInteriorUnitEdges.channels Q).filter fun ab ↦ 5 ≤ ab.2

theorem uniform_bound (F : Finset (ℕ × ℕ))
    (hF : ∀ ab ∈ F, 0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.1.Coprime ab.2 ∧ 5 ≤ ab.2)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℕ × ℕ → ℕ,
        orderedMass N L (edges F N L H) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  have hlocal (ab : F) : ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      PrimitiveNominalMass.mass (PrivateChannelActivity.pairs N H ab.val.1 ab.val.2 L) L ≤
        K * L * (N : ℝ) ^ (-1 + 1 / (ab.val.2 : ℝ)) := by
    obtain ⟨ha, hab, hcop, _hb⟩ := hF ab.val ab.property
    exact HomogeneousChannelMass.uniform_fixed_channel C ab.val.1 ab.val.2 ha hab hcop
  choose K hK Nc _hNc hc using hlocal
  let A := ∑ ab : F, K ab
  have hA : 0 ≤ A := sum_nonneg (fun ab _ ↦ (hK ab).le)
  obtain ⟨NG, _hNG, hg⟩ := FixedPrivateChannelDisjoint.uniform_geometry F
    (fun ab hab ↦ ⟨(hF ab hab).1, (hF ab hab).2.1⟩) C
  obtain ⟨NP, hp⟩ := UnorderedSeedMassPropagation.uniform_mass 2 (by omega) 1 C (ε / 4) (by positivity)
  obtain ⟨NA, ha⟩ := FixedChannelAlignedTargetMass.uniform_polynomial C A (ε / 4) hA 1 (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 36 (-4 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 10 (max (univ.sup Nc) (max NG (max NP (max NA NF)))), by omega, ?_⟩
  intro N hN L hband H
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hgeom := hg N (by omega) L hband
  have hlarge (ab : ℕ × ℕ) (hab : ab ∈ F) := (hgeom.2.2 ab hab).1
  have hsource := source_data (by omega : 2 ≤ N) hgeom.1
    (fun ab hab ↦ ⟨(hF ab hab).1, (hF ab hab).2.1, (hF ab hab).2.2.1⟩) hlarge H
  have hthreshold (ab : F) : Nc ab ≤ N := (le_sup (f := Nc) (mem_univ ab)).trans (by omega)
  have hchannel (ab : F) : beta N (H ab.val) ab.val.1 ab.val.2 L ≤
      K ab * L * (N : ℝ) ^ (-4 / 5 : ℝ) := by
    have hcomp : beta N (H ab.val) ab.val.1 ab.val.2 L ≤
        PrimitiveNominalMass.mass (PrivateChannelActivity.pairs N (H ab.val) ab.val.1 ab.val.2 L) L := by
      calc
        _ ≤ ∑ e ∈ CompatibleChannelEdges.edges N (H ab.val) ab.val.1 ab.val.2 L, HomogeneousRunMass.probability L e :=
          sum_le_sum (fun e _ ↦ HomogeneousRunMass.actual_joint_le L hgeom.1 e)
        _ ≤ ∑ e ∈ PrivateChannelActivity.pairs N (H ab.val) ab.val.1 ab.val.2 L, HomogeneousRunMass.probability L e :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun e _ _ ↦ (HomogeneousRunMass.probability_pos L e).le)
        _ = _ := sum_congr rfl (fun e he ↦ HomogeneousRunMass.regular_weight
          (PrivateChannelRank.regular (by omega : 2 ≤ N) (hF ab.val ab.property).1 (hF ab.val ab.property).2.1 he))
    have hpower : (N : ℝ) ^ (-1 + 1 / (ab.val.2 : ℝ)) ≤ (N : ℝ) ^ (-4 / 5 : ℝ) := by
      have hrecip : 1 / (ab.val.2 : ℝ) ≤ 1 / 5 :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 5) (by exact_mod_cast (hF ab.val ab.property).2.2.2)
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hrecip])
    exact (hcomp.trans (hc ab N (hthreshold ab) L (H ab.val) hband)).trans
      (mul_le_mul_of_nonneg_left hpower (mul_nonneg (hK ab).le (Nat.cast_nonneg L)))
  have hB : (∑ e ∈ edges F N L H, infiniteJointMoment L e) ≤ (N : ℝ) ^ (-4 / 5 + ε / 4) := by
    have hcover := GraphStarWeights.sum_biUnion_le_nonneg F
      (fun ab ↦ CompatibleChannelEdges.edges N (H ab) ab.1 ab.2 L) (infiniteJointMoment L) (infiniteJointMoment_nonneg L)
    have hsum : (∑ e ∈ edges F N L H, infiniteJointMoment L e) ≤ ∑ ab : F, beta N (H ab.val) ab.val.1 ab.val.2 L := by
      exact hcover.trans_eq (sum_coe_sort F (fun ab ↦ beta N (H ab) ab.1 ab.2 L)).symm
    have hAL : A * (L : ℝ) ≤ (N : ℝ) ^ (ε / 4) := by
      have hh := ha N (by omega) L hband
      simp only [pow_one] at hh
      exact (mul_le_mul_of_nonneg_left (by exact_mod_cast (Nat.le_succ L)) hA).trans hh
    calc
      _ ≤ ∑ ab : F, beta N (H ab.val) ab.val.1 ab.val.2 L := hsum
      _ ≤ ∑ ab : F, K ab * L * (N : ℝ) ^ (-4 / 5 : ℝ) := sum_le_sum (fun ab _ ↦ hchannel ab)
      _ = A * L * (N : ℝ) ^ (-4 / 5 : ℝ) := by rw [← sum_mul, ← sum_mul]
      _ ≤ (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (-4 / 5 : ℝ) := mul_le_mul_of_nonneg_right hAL (by positivity)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  let E := edges F N L H
  have hE : ∀ e ∈ E, e ⊆ dyadicBlock N ∧ e.card = 2 := fun e he ↦ ⟨(hsource e he).1, (hsource e he).2.1⟩
  have hprop := hp N (by omega) L hgeom.1 hband E hE (PairGeneratedTripleWeights.families (dyadicBlock N) E)
    (fun _ hI ↦ PairGeneratedTripleWeights.family_data hE hI)
  norm_num only [Nat.factorial, Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat] at hprop
  rw [ordered_mass_eq N L E hE]
  calc
    _ ≤ 6 * (6 * (N : ℝ) ^ (ε / 4) * ∑ e ∈ E, infiniteJointMoment L e) :=
      mul_le_mul_of_nonneg_left hprop (by norm_num)
    _ ≤ 6 * (6 * (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (-4 / 5 + ε / 4)) := by gcongr
    _ = 36 * (N : ℝ) ^ (-4 / 5 + ε / 2) := by
      rw [mul_assoc (6 : ℝ), ← Real.rpow_add hn,
        show ε / 4 + (-4 / 5 + ε / 4) = -4 / 5 + ε / 2 by ring]
      ring
    _ ≤ _ := by simpa only [show (-4 / 5 + ε / 2) + ε / 2 = -4 / 5 + ε by ring] using hf N (by omega)

theorem uniform_original (F : Finset (ℕ × ℕ))
    (hF : ∀ ab ∈ F, 0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.1.Coprime ab.2 ∧ 5 ≤ ab.2)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℕ × ℕ → ℕ,
        orderedMass N L (rawEdges F N L H) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨NB, _hNB, hb⟩ := uniform_bound F hF C ε hε
  obtain ⟨NG, _hNG, hg⟩ := FixedPrivateChannelDisjoint.uniform_geometry F
    (fun ab hab ↦ ⟨(hF ab hab).1, (hF ab hab).2.1⟩) C
  refine ⟨max 10 (max NB NG), by omega, ?_⟩
  intro N hN L hband H
  have hlarge (ab : ℕ × ℕ) (hab : ab ∈ F) := ((hg N (by omega) L hband).2.2 ab hab).1
  rw [raw_ordered_mass_eq (by omega : 2 ≤ N) (fun ab hab ↦ (hF ab hab).2.1) hlarge H]
  exact hb N (by omega) L hband H

theorem height_cutoff (Q : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℕ × ℕ → ℕ,
        orderedMass N L (rawEdges (channels Q) N L H) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  apply uniform_original (channels Q) _ C ε hε
  intro ab hab
  obtain ⟨habC, hb5⟩ := mem_filter.mp hab
  obtain ⟨ha, hlt, _hint, hcop, _haQ, _hbQ⟩ := FiniteInteriorUnitEdges.channel_data habC
  exact ⟨ha, hlt, hcop, hb5⟩

end PaperP1.FiniteHighChannelTripleMass
