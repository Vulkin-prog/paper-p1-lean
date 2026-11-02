module

public import PaperP1.Asymptotics.RationalTripleEvenMass
public import PaperP1.Asymptotics.ThreeSlopePositiveActivity

/-! # The extremal private witnesses realize the sharp exponent in the larger even-rank sector -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalTripleEvenSharpMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PrivateNormalizedFamilies PaperP1.ThreeSlopeProgressions PaperP1.ThreeSlopePrivatePopulation

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def lowerConstant (C : ℝ) : ℝ := ThreeSlopePositiveActivity.jointConstant C / 120

theorem lower_constant_pos (C : ℝ) : 0 < lowerConstant C :=
  div_pos (ThreeSlopePositiveActivity.joint_constant_pos C) (by norm_num)

theorem extremal_normalization (t : ℕ) :
    RationalTripleNormalizers.centres 10 12 15 t = centres t := rfl

theorem extremal_even_rank {t L : ℕ} (ht : 1 ≤ t)
    (hprivate : FiniteEvenSquareClasses.Private (valueUnion step (centres t) L)) :
    EvenIndependentValues.Independent
      (valueUnion (RationalTripleNormalizers.scale 10 12 15) (RationalTripleNormalizers.centres 10 12 15 t) L) := by
  have hs : RationalTripleNormalizers.scale 10 12 15 = (fun i ↦ 30 * step i) := by
    funext i
    fin_cases i <;> norm_num [RationalTripleNormalizers.scale, step]
  rw [extremal_normalization, hs]
  exact (NormalizedFamilyDilation.even_independent_dilate_iff (by decide : 0 < 30)
    step (centres t) step_pos (centres_ge_two ht)).2 (EvenIndependentValues.of_private _ hprivate)

theorem witness_mem_hosts {N L k t : ℕ} (hN : 10 ≤ N) (hL : 15 ≤ L + 1) (hk : 1 ≤ k)
    (ht : t ∈ good N L) : centres t ∈ RationalTripleEvenMass.hosts N L k false := by
  have hd := mem_filter.mp ht
  have htpos := (parameter_bounds hN hd.1).1
  have hheight : 15 ≤ (L + 1) ^ k := hL.trans (le_self_pow (by omega) (by omega : k ≠ 0))
  simpa only [extremal_normalization] using RationalTripleEvenMass.mem_hosts_of_source false
    (by decide : 10 < 12) (by decide : 12 < 15) (by decide : 15 < 2 * 10) (by decide)
    htpos hheight (centres_dyadic hN hd.1) (extremal_even_rank htpos hd.2.private) (by simp)

theorem witness_families_subset {N L k : ℕ} (hN : 10 ≤ N) (hL : 15 ≤ L + 1) (hk : 1 ≤ k) :
    ThreeSlopePositiveActivity.families N L ⊆ RationalTripleEvenMass.unorderedFamilies N L k false := by
  intro T hT
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hT
  exact mem_image.mpr ⟨centres t, witness_mem_hosts hN hL hk ht, rfl⟩

theorem witness_joint_lower (C : ℝ) :
    ∃ N₀ : ℕ, 1000 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      lowerConstant C * (N : ℝ) ^ (-41 / 30 : ℝ) ≤
        ∑ T ∈ ThreeSlopePositiveActivity.families N L, infiniteJointMoment L T := by
  obtain ⟨N₀, hN₀, hu⟩ := ThreeSlopePrivateDensity.linear_good_population C
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  obtain ⟨hL, hpop, hgood⟩ := hu N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpoint (T : Finset ℕ) (hT : T ∈ ThreeSlopePositiveActivity.families N L) :
      ThreeSlopePositiveActivity.jointConstant C * (N : ℝ) ^ (-71 / 30 : ℝ) ≤ infiniteJointMoment L T := by
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hT
    have hd := hgood t ht
    exact ThreeSlopePositiveActivity.point_probability_lower (by omega) hd.1 (by omega) hband hd.2.2
  have hnon : 0 ≤ ThreeSlopePositiveActivity.jointConstant C * (N : ℝ) ^ (-71 / 30 : ℝ) :=
    mul_nonneg (ThreeSlopePositiveActivity.joint_constant_pos C).le (Real.rpow_nonneg hn.le _)
  calc
    _ = ((N : ℝ) / 120) * (ThreeSlopePositiveActivity.jointConstant C * (N : ℝ) ^ (-71 / 30 : ℝ)) := by
      have hpow : (N : ℝ) * (N : ℝ) ^ (-71 / 30 : ℝ) = (N : ℝ) ^ (-41 / 30 : ℝ) := by
        calc
          _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-71 / 30 : ℝ) := by rw [Real.rpow_one]
          _ = (N : ℝ) ^ (1 + (-71 / 30 : ℝ)) := by rw [Real.rpow_add hn]
          _ = _ := by norm_num
      dsimp only [lowerConstant]
      rw [← hpow]
      ring
    _ ≤ ((good N L).card : ℝ) * (ThreeSlopePositiveActivity.jointConstant C * (N : ℝ) ^ (-71 / 30 : ℝ)) :=
      mul_le_mul_of_nonneg_right hpop hnon
    _ = ∑ _T ∈ ThreeSlopePositiveActivity.families N L,
        ThreeSlopePositiveActivity.jointConstant C * (N : ℝ) ^ (-71 / 30 : ℝ) := by
      rw [sum_const, nsmul_eq_mul, ThreeSlopePositiveActivity.families_card]
    _ ≤ ∑ T ∈ ThreeSlopePositiveActivity.families N L, infiniteJointMoment L T := sum_le_sum hpoint

theorem unordered_lower (C : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ∃ N₀ : ℕ, 1000 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      lowerConstant C * (N : ℝ) ^ (-41 / 30 : ℝ) ≤ RationalTripleEvenMass.unorderedMass N L k false := by
  obtain ⟨NA, _hNA, ha⟩ := witness_joint_lower C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 15
  refine ⟨max 1000 (max NA NG), by omega, ?_⟩
  intro N hN L hband
  exact (ha N (by omega) L hband).trans
    (sum_le_sum_of_subset_of_nonneg (witness_families_subset (by omega) (hg N (by omega) L hband).2.1 hk)
      (fun T _ _ ↦ infiniteJointMoment_nonneg L T))

theorem uniform_sharp_mass (C : ℝ) (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1000 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      lowerConstant C * (N : ℝ) ^ (-41 / 30 : ℝ) ≤ RationalTripleEvenMass.unorderedMass N L k false ∧
      RationalTripleEvenMass.unorderedMass N L k false ≤ RationalTripleEvenMass.mass N L k false ∧
      RationalTripleEvenMass.mass N L k false ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NA, _hNA, ha⟩ := unordered_lower C k hk
  obtain ⟨NB, _hNB, hb⟩ := RationalTripleEvenMass.uniform_full_mass C k ε hε
  refine ⟨max 1000 (max NA NB), by omega, ?_⟩
  intro N hN L hband
  exact ⟨ha N (by omega) L hband, RationalTripleEvenMass.unordered_mass_le N L k false,
    hb N (by omega) L hband⟩

theorem nonextremal_relative_mass (C : ℝ) (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1000 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      RationalTripleEvenMass.unorderedMass N L k true ≤
        (lowerConstant C)⁻¹ * (N : ℝ) ^ (-1 / 45 + ε) * RationalTripleEvenMass.unorderedMass N L k false := by
  obtain ⟨NA, _hNA, ha⟩ := unordered_lower C k hk
  obtain ⟨NB, _hNB, hb⟩ := RationalTripleEvenMass.uniform_unordered_nonextremal_mass C k ε hε
  refine ⟨max 1000 (max NA NB), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc := lower_constant_pos C
  have hh := mul_le_mul_of_nonneg_left (ha N (by omega) L hband)
    (mul_nonneg (inv_nonneg.mpr hc.le) (Real.rpow_nonneg hn.le (-1 / 45 + ε)))
  have heq : ((lowerConstant C)⁻¹ * (N : ℝ) ^ (-1 / 45 + ε)) *
      (lowerConstant C * (N : ℝ) ^ (-41 / 30 : ℝ)) = (N : ℝ) ^ (-25 / 18 + ε) := by
    calc
      _ = ((lowerConstant C)⁻¹ * lowerConstant C) *
          ((N : ℝ) ^ (-1 / 45 + ε) * (N : ℝ) ^ (-41 / 30 : ℝ)) := by ring
      _ = (N : ℝ) ^ ((-1 / 45 + ε) + (-41 / 30 : ℝ)) := by
        rw [inv_mul_cancel₀ hc.ne', one_mul, ← Real.rpow_add hn]
      _ = _ := by congr 1; ring
  rw [heq] at hh
  exact (hb N (by omega) L hband).trans hh

theorem nonextremal_negligible (C : ℝ) (k : ℕ) (hk : 1 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 1000 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      RationalTripleEvenMass.unorderedMass N L k true ≤
        δ * RationalTripleEvenMass.unorderedMass N L k false := by
  obtain ⟨NA, _hNA, ha⟩ := nonextremal_relative_mass C k hk (1 / 90) (by norm_num)
  have ht : Filter.Tendsto (fun N : ℕ ↦ (lowerConstant C)⁻¹ * (N : ℝ) ^ (-1 / 90 : ℝ))
      Filter.atTop (nhds 0) := by
    have hh := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 90)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (lowerConstant C)⁻¹
    simpa only [Function.comp_def, neg_div, mul_zero] using hh
  obtain ⟨NB, hb⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
  refine ⟨max 1000 (max NA NB), by omega, ?_⟩
  intro N hN L hband
  have hh := ha N (by omega) L hband
  norm_num only [show (-1 / 45 : ℝ) + 1 / 90 = -1 / 90 by norm_num] at hh
  have hsmall : (lowerConstant C)⁻¹ * (N : ℝ) ^ (-(1 / 90 : ℝ)) ≤ δ := by
    simpa only [neg_div] using (hb N (by omega)).le
  exact hh.trans (mul_le_mul_of_nonneg_right hsmall
    (sum_nonneg (fun T _ ↦ infiniteJointMoment_nonneg L T)))

end PaperP1.RationalTripleEvenSharpMass
