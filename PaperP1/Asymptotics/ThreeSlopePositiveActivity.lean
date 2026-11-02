module

public import PaperP1.Asymptotics.ThreeSlopePrivateDensity
public import PaperP1.Model.PositiveMarginalRestriction

/-! # The unconditional N^(-41/30) lower bound for positive connected triple activity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ThreeSlopePositiveActivity

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.RegularStarts
  PaperP1.ThreeSlopeProgressions PaperP1.ThreeSlopeValueCounts PaperP1.ThreeSlopeWitnessMass
  PaperP1.ThreeSlopeWitnessActivity PaperP1.PrivateNormalizedFamilies PaperP1.ThreeSlopePrivatePopulation

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def jointConstant (C : ℝ) : ℝ := (2 : ℝ) ^ (-4 - (71 / 30 : ℝ) * C)
def lowerConstant (C : ℝ) : ℝ := jointConstant C / 240

theorem joint_constant_pos (C : ℝ) : 0 < jointConstant C := Real.rpow_pos_of_pos (by norm_num) _
theorem lower_constant_pos (C : ℝ) : 0 < lowerConstant C := div_pos (joint_constant_pos C) (by norm_num)

theorem point_probability_lower {N L t : ℕ} {C : ℝ} (hN : 2 ≤ N) (ht : 1 ≤ t) (hL : 1 ≤ L)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C)
    (hprivate : FiniteEvenSquareClasses.Private (valueUnion step (centres t) L)) :
    jointConstant C * (N : ℝ) ^ (-71 / 30 : ℝ) ≤ infiniteJointMoment L (support t) := by
  let R := (valueUnion step (centres t) L).card - 1
  have hdim : (R : ℝ) + (nullity L : ℝ) = 3 * L := by exact_mod_cast nullity_rank_identity ht hL
  have hlow := (nullity_bounds L hL).1
  have hR : (R : ℝ) ≤ (71 / 30 : ℝ) * L + 4 := by linarith only [hdim, hlow]
  have hhigh : (L : ℝ) ≤ Real.log N / Real.log 2 + C := by have hh := (abs_le.mp hband).2; linarith
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hhigh hlogtwo.le
  rw [add_mul, div_mul_cancel₀ _ hlogtwo.ne'] at hmul
  have hRmul := mul_le_mul_of_nonneg_right hR hlogtwo.le
  have hlog : Real.log 2 * (-4 - (71 / 30 : ℝ) * C) + Real.log N * (-71 / 30 : ℝ) ≤
      Real.log 2 * (-(R : ℝ)) := by nlinarith only [hmul, hRmul]
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hq : infiniteJointMoment L (support t) = (2 : ℝ) ^ (-(R : ℝ)) := by
    have hh := PrivateNormalizedFamilyRank.actual_probability (by omega : 0 < 3) step (centres t)
      step_pos (centres_ge_two ht) (by omega) (60 * t) (common_mem ht (by omega)) hprivate (exclusive ht L)
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    exact hh
  rw [hq, jointConstant, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos hn, ← Real.exp_add, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact Real.exp_le_exp.mpr hlog

theorem support_injective : Function.Injective support := by
  intro t u hh
  have ht : 10 * t ∈ support u := by rw [← hh, support_eq]; exact mem_insert_self _ _
  have hu : 10 * u ∈ support t := by rw [hh, support_eq]; exact mem_insert_self _ _
  simp only [support_eq, mem_insert, mem_singleton] at ht hu
  omega

def families (N L : ℕ) : Finset (Finset ℕ) := (good N L).image support

theorem families_card (N L : ℕ) : (families N L).card = (good N L).card :=
  card_image_of_injective _ support_injective

theorem families_data {N L : ℕ} (hN : 10 ≤ N) (hL : 60 ≤ L) {T : Finset ℕ} (hT : T ∈ families N L) :
    T ⊆ regularStarts N L ∧ T.card = 3 ∧ ConnectedWindowFamilies.Connected L T ∧
      0 < infiniteJointMoment L T := by
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hT
  have htdata := mem_filter.mp ht
  have htb := parameter_bounds hN htdata.1
  have hpriv := htdata.2.private
  refine ⟨?_, support_card htb.1, connected htb.1 hL hpriv, ?_⟩
  · intro x hx
    obtain ⟨i, _hi, rfl⟩ := mem_image.mp hx
    exact mem_regularStarts.mpr ⟨centres_dyadic hN htdata.1 i,
      PrivateNormalizedFamilyRank.local_ranks step (centres t) step_pos (centres_ge_two htb.1) hpriv i⟩
  · rw [joint_probability htb.1 (by omega) hpriv]
    positivity

theorem positive_connected_lower (C : ℝ) :
    ∃ N₀ : ℕ, 1000 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, regularStarts N L ⊆ G →
      lowerConstant C * (N : ℝ) ^ (-41 / 30 : ℝ) ≤
        TripleActivityConnected.positiveConnected L (G.powersetCard 3) := by
  obtain ⟨N₀, hN₀, hu⟩ := ThreeSlopePrivateDensity.linear_good_population C
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG
  obtain ⟨hL, hpop, hgood⟩ := hu N hN L hband
  have hN10 : 10 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let W := (G.powersetCard 3).filter fun T ↦ ConnectedWindowFamilies.Connected L T ∧ 0 < infiniteJointMoment L T
  have hsub : families N L ⊆ W := by
    intro T hT
    obtain ⟨hreg, hcard, hconn, hq⟩ := families_data hN10 hL hT
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hreg.trans hG, hcard⟩, hconn, hq⟩
  have hpoint (T : Finset ℕ) (hT : T ∈ families N L) :
      (jointConstant C / 2) * (N : ℝ) ^ (-71 / 30 : ℝ) ≤ infiniteCenteredCoefficient L T := by
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hT
    have hd := hgood t ht
    have hp := point_probability_lower (by omega) hd.1 (by omega) hband hd.2.2
    have hc := half_joint_lower hd.1 hL hd.2.2
    linarith only [hp, hc]
  have hnon : 0 ≤ (jointConstant C / 2) * (N : ℝ) ^ (-71 / 30 : ℝ) :=
    mul_nonneg (div_nonneg (joint_constant_pos C).le (by norm_num)) (Real.rpow_nonneg hn.le _)
  calc
    _ = ((N : ℝ) / 120) * ((jointConstant C / 2) * (N : ℝ) ^ (-71 / 30 : ℝ)) := by
      have hpow : (N : ℝ) * (N : ℝ) ^ (-71 / 30 : ℝ) = (N : ℝ) ^ (-41 / 30 : ℝ) := by
        calc
          _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-71 / 30 : ℝ) := by rw [Real.rpow_one]
          _ = (N : ℝ) ^ (1 + (-71 / 30 : ℝ)) := by rw [Real.rpow_add hn]
          _ = _ := by norm_num
      dsimp only [lowerConstant]
      rw [← hpow]
      ring
    _ ≤ ((good N L).card : ℝ) * ((jointConstant C / 2) * (N : ℝ) ^ (-71 / 30 : ℝ)) :=
      mul_le_mul_of_nonneg_right hpop hnon
    _ = ∑ _T ∈ families N L, (jointConstant C / 2) * (N : ℝ) ^ (-71 / 30 : ℝ) := by
      rw [sum_const, nsmul_eq_mul, families_card]
    _ ≤ ∑ T ∈ families N L, infiniteCenteredCoefficient L T := sum_le_sum hpoint
    _ ≤ ∑ T ∈ W, infiniteCenteredCoefficient L T := sum_le_sum_of_subset_of_nonneg hsub
      (fun T hT _ ↦ CompatibleRunCentered.coefficient_nonneg L T (by omega) (mem_filter.mp hT).2.2)
    _ = _ := rfl

theorem dyadic_positive_lower (C : ℝ) :
    ∃ N₀ : ℕ, 1000 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      lowerConstant C * (N : ℝ) ^ (-41 / 30 : ℝ) ≤
        TripleActivityConnected.positiveConnected L ((dyadicBlock N).powersetCard 3) := by
  obtain ⟨N₀, hN₀, hu⟩ := positive_connected_lower C
  exact ⟨N₀, hN₀, fun N hN L hband ↦ hu N hN L hband _ (regularStarts_subset N L)⟩

/-- The positive connected activity on the exact admissible original ground of the source. -/
theorem source_positive_lower (C : ℝ) :
    ∃ N₀ : ℕ, 1000 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      lowerConstant C * (N : ℝ) ^ (-41 / 30 : ℝ) ≤
        TripleActivityConnected.positiveConnected L
          ((PositiveMarginalRestriction.positiveGround (dyadicBlock N) L).powersetCard 3) := by
  obtain ⟨NP, _hNP, hp⟩ := positive_connected_lower C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 61
  refine ⟨max 1000 (max NP NG), by omega, ?_⟩
  intro N hN L hband
  have hwidth := (hg N (by omega) L hband).2.1
  apply hp N (by omega) L hband
  intro x hx
  have hxN := (mem_Ico.mp (mem_regularStarts.mp hx).1).1
  apply mem_filter.mpr
  refine ⟨regularStarts_subset N L hx, ?_⟩
  rw [marginal_on_regular (by omega) (by omega) hx]
  positivity

end PaperP1.ThreeSlopePositiveActivity
