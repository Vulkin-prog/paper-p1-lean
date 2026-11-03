module

public import PaperP1.Asymptotics.DensePrimitiveTripleRankMassUnderBCN
public import PaperP1.Asymptotics.LowPrimitiveTripleRankMass
public import PaperP1.Model.PrimitiveActualMass

/-! # All primitive true-window triples have rank and actual activity of power three halves

The low-nullity part is unconditional; dense confinement uses the existing
explicit BCN input. Zero marginals and incompatible affine systems are retained.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveTripleMassUnderBCN

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies PaperP1.PrimitiveWindowMass

theorem uniform_rank_mass (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = 3 ∧ Primitive L I) →
        mass F L ≤ (N : ℝ) ^ (-(3 : ℝ) / 2 + ε) := by
  classical
  obtain ⟨b, hb⟩ := exists_nat_gt (max 1 (4 / ε))
  have hbR : (0 : ℝ) < b := lt_trans (by norm_num) ((le_max_left _ _).trans_lt hb)
  have hbN : 0 < b := by exact_mod_cast hbR
  have hprod : 4 < (b : ℝ) * ε := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hb)
  have hsmall : 1 / (b : ℝ) ≤ ε / 4 := (div_le_iff₀ hbR).mpr (by nlinarith only [hprod])
  obtain ⟨ND, _hND, hd⟩ := DensePrimitiveTripleRankMassUnderBCN.uniform_rank_mass
    c κ hc hBCN C (1 / (b : ℝ)) (ε / 2) (by positivity) (by positivity)
  obtain ⟨NL, _hNL, hl⟩ := LowPrimitiveTripleRankMass.uniform_bound b hbN C (ε / 4) (by positivity)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption 2 (-(3 : ℝ) / 2 + ε / 2)
    (ε / 2) (by positivity)
  refine ⟨3 + ND + NL + NA, by omega, ?_⟩
  intro N hN L hband F hF
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let P := fun I ↦ (1 / (b : ℝ)) * L ≤ (runRelativeNullity L I : ℝ)
  let FD := F.filter P
  let FL := F.filter fun I ↦ ¬P I
  have hdense : mass FD L ≤ (N : ℝ) ^ (-(3 : ℝ) / 2 + ε / 2) := by
    have hh := hd N (by omega) L hband FD (by
      intro I hI
      obtain ⟨hIF, hdim⟩ := mem_filter.mp hI
      obtain ⟨hdyadic, hcard, hprim⟩ := hF I hIF
      exact ⟨hcard, hdyadic, hprim, hdim⟩)
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  have hlow : mass FL L ≤ (N : ℝ) ^ (-(3 : ℝ) / 2 + ε / 2) := by
    have hh := hl N (by omega) L hband FL (by
      intro I hI
      obtain ⟨hIF, hdim⟩ := mem_filter.mp hI
      obtain ⟨hdyadic, hcard, hprim⟩ := hF I hIF
      refine ⟨hdyadic, hcard, hprim, ?_⟩
      have hlt : (runRelativeNullity L I : ℝ) < (1 / (b : ℝ)) * L := lt_of_not_ge hdim
      have he : (1 / (b : ℝ)) * L = (L : ℝ) / b := by ring
      exact he ▸ hlt)
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hsmall]))
  calc
    _ = mass FD L + mass FL L := (sum_filter_add_sum_filter_not F P (weight L)).symm
    _ ≤ 2 * (N : ℝ) ^ (-(3 : ℝ) / 2 + ε / 2) := by linarith only [hdense, hlow]
    _ ≤ (N : ℝ) ^ ((-(3 : ℝ) / 2 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_actual_activity (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = 3 ∧ Primitive L I) →
      (∑ I ∈ F, (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|)) ≤
        (N : ℝ) ^ (-(3 : ℝ) / 2 + ε) := by
  obtain ⟨NM, _hNM, hm⟩ := uniform_rank_mass c κ hc hBCN C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption 2 (-(3 : ℝ) / 2 + ε / 2)
    (ε / 2) (by positivity)
  refine ⟨3 + NM + NG + NA, by omega, ?_⟩
  intro N hN L hband F hF
  have hL : 0 < L := by have hh := hg N (by omega) L hband; omega
  have hpoint (I : Finset ℕ) (hI : I ∈ F) :
      infiniteJointMoment L I + |infiniteCenteredCoefficient L I| ≤ 2 * weight L I := by
    have hq := joint_le_weight L hL I
    have hc := PrimitiveActualMass.centered_le_weight L hL I (card_pos.mp (by rw [(hF I hI).2.1]; omega))
    linarith only [hq, hc]
  calc
    _ ≤ ∑ I ∈ F, 2 * weight L I := sum_le_sum hpoint
    _ = 2 * mass F L := by rw [← mul_sum]; rfl
    _ ≤ 2 * (N : ℝ) ^ (-(3 : ℝ) / 2 + ε / 2) := mul_le_mul_of_nonneg_left
      (hm N (by omega) L hband F hF) (by norm_num)
    _ ≤ (N : ℝ) ^ ((-(3 : ℝ) / 2 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

theorem companion_T8_2 (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = 3 ∧ Primitive L I ∧
          η * ((L + 1 : ℕ) : ℝ) ≤ (runRelativeNullity L I : ℝ)) →
          (F.card : ℝ) ≤ (N : ℝ) ^ ε ∧ mass F L ≤ (N : ℝ) ^ (-2 + ε)) ∧
      (∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = 3 ∧ Primitive L I) →
          (∑ I ∈ F, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-(3 : ℝ) / 2 + ε)) := by
  obtain ⟨NH, _hNH, hh⟩ := DensePrimitiveTripleHostsUnderBCN.companion_T8_2_hosts
    c κ hc hBCN C η ε hη hε
  obtain ⟨NM, _hNM, hm⟩ := DensePrimitiveTripleRankMassUnderBCN.uniform_rank_mass
    c κ hc hBCN C η ε hη hε
  obtain ⟨NA, _hNA, ha⟩ := uniform_actual_activity c κ hc hBCN C ε hε
  refine ⟨3 + NH + NM + NA, by omega, ?_⟩
  intro N hN L hband
  constructor
  · intro F hF
    refine ⟨hh N (by omega) L hband F (fun I hI ↦
      ⟨(hF I hI).2.1, (hF I hI).1, (hF I hI).2.2.1, (hF I hI).2.2.2⟩), ?_⟩
    apply hm N (by omega) L hband F
    intro I hI
    obtain ⟨hdyadic, hcard, hprim, hdense⟩ := hF I hI
    refine ⟨hcard, hdyadic, hprim, ?_⟩
    push_cast at hdense
    linarith only [hdense, hη]
  · intro F hF
    apply le_trans (sum_le_sum fun I _hI ↦ ?_) (ha N (by omega) L hband F hF)
    exact le_add_of_nonneg_left (infiniteJointMoment_nonneg L I)

end PaperP1.PrimitiveTripleMassUnderBCN
