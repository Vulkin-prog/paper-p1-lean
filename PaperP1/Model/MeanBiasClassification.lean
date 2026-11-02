module

public import PaperP1.Model.MeanBiasQuantization
public import PaperP1.Model.RegularSetAsymptotic
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # The critical mean bias as a difference of two actual window counts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MeanBiasClassification

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.MeanBiasQuantization
  PaperP1.RegularStarts PaperP1.Arithmetic PaperP1.CountObservables

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def zeroStarts (N L : ℕ) : Finset ℕ := (dyadicBlock N).filter fun x ↦ localMultiplicity x L = 0

def doubleStarts (N L : ℕ) : Finset ℕ := (dyadicBlock N).filter fun x ↦ localMultiplicity x L = 2

theorem multiplicity_zero_iff {x L : ℕ} (hx : 0 < x) (hL : 0 < L) :
    localMultiplicity x L = 0 ↔ infiniteMarginal x L = 0 := by
  constructor
  · intro h
    rw [nominal_times_multiplicity hx hL, h, Nat.cast_zero, mul_zero]
  · intro h
    simp only [localMultiplicity, h, lt_self_iff_false, ite_eq_right_iff]
    simp

theorem multiplicity_two_iff {x L : ℕ} (hx : 0 < x) (hL : 0 < L) :
    localMultiplicity x L = 2 ↔ infiniteMarginal x L = 2 * (2 ^ L : ℝ)⁻¹ := by
  constructor
  · intro h
    rw [nominal_times_multiplicity hx hL, h]
    norm_num
    ring
  · intro h
    have hm := nominal_times_multiplicity hx hL
    rw [h] at hm
    have hp : 0 < (2 ^ L : ℝ)⁻¹ := by positivity
    have hi : (localMultiplicity x L : ℝ) = 2 := by nlinarith only [hm, hp]
    exact_mod_cast hi

theorem zeroStarts_source {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    zeroStarts N L = (dyadicBlock N).filter fun x ↦ infiniteMarginal x L = 0 := by
  ext x
  simp only [zeroStarts, mem_filter]
  by_cases hx : x ∈ dyadicBlock N
  · have hxpos : 0 < x := by have h := (mem_Ico.mp hx).1; omega
    exact and_congr_right (fun _ ↦ multiplicity_zero_iff hxpos hL)
  · simp only [hx, false_and]

theorem doubleStarts_source {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    doubleStarts N L = (dyadicBlock N).filter fun x ↦ infiniteMarginal x L = 2 * (2 ^ L : ℝ)⁻¹ := by
  ext x
  simp only [doubleStarts, mem_filter]
  by_cases hx : x ∈ dyadicBlock N
  · have hxpos : 0 < x := by have h := (mem_Ico.mp hx).1; omega
    exact and_congr_right (fun _ ↦ multiplicity_two_iff hxpos hL)
  · simp only [hx, false_and]

theorem coefficient_count_form (x L : ℕ) (hd : deficiency x L ≤ 1) :
    coefficient x L = (if localMultiplicity x L = 2 then 1 else 0) -
      (if localMultiplicity x L = 0 then 1 else 0) := by
  by_cases hp : 0 < infiniteMarginal x L
  · have hcases : deficiency x L = 0 ∨ deficiency x L = 1 := by omega
    rcases hcases with h | h <;> norm_num [coefficient, localMultiplicity, hp, h]
  · simp only [coefficient, localMultiplicity, ite_eq_right hp, Nat.cast_zero]
    norm_num

theorem bias_count_identity (N L : ℕ) (hd : ∀ x ∈ dyadicBlock N, deficiency x L ≤ 1) :
    bias (dyadicBlock N) L = (doubleStarts N L).card - (zeroStarts N L).card := by
  have hdouble : (∑ x ∈ dyadicBlock N, if localMultiplicity x L = 2 then (1 : ℤ) else 0) =
      (doubleStarts N L).card := by
    rw [← sum_filter]
    simp only [doubleStarts, sum_const, nsmul_eq_mul, mul_one]
  have hzero : (∑ x ∈ dyadicBlock N, if localMultiplicity x L = 0 then (1 : ℤ) else 0) =
      (zeroStarts N L).card := by
    rw [← sum_filter]
    simp only [zeroStarts, sum_const, nsmul_eq_mul, mul_one]
  rw [bias, ← hdouble, ← hzero, ← sum_sub_distrib]
  exact sum_congr rfl (fun x hx ↦ coefficient_count_form x L (hd x hx))

theorem multiplicity_on_regular {N L x : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (hx : x ∈ regularStarts N L) :
    localMultiplicity x L = 1 := by
  have hxpos : 0 < x := by have h := (mem_Ico.mp (mem_regularStarts.mp hx).1).1; omega
  have hp : 0 < infiniteMarginal x L := by rw [marginal_on_regular hxpos hL hx]; positivity
  simp only [localMultiplicity, ite_eq_left hp, deficiency, (mem_regularStarts.mp hx).2,
    Nat.sub_self, pow_zero]

theorem zeroStarts_subset_irregular {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    zeroStarts N L ⊆ irregularStarts N L := by
  intro x hx
  obtain ⟨hblock, hzero⟩ := mem_filter.mp hx
  apply mem_sdiff.mpr
  refine ⟨hblock, ?_⟩
  intro hreg
  have h := multiplicity_on_regular hN hL hreg
  omega

theorem doubleStarts_subset_irregular {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    doubleStarts N L ⊆ irregularStarts N L := by
  intro x hx
  obtain ⟨hblock, htwo⟩ := mem_filter.mp hx
  apply mem_sdiff.mpr
  refine ⟨hblock, ?_⟩
  intro hreg
  have h := multiplicity_on_regular hN hL hreg
  omega

theorem abs_bias_le_irregular {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hd : ∀ x ∈ dyadicBlock N, deficiency x L ≤ 1) :
    |bias (dyadicBlock N) L| ≤ (irregularStarts N L).card := by
  have hz : ((zeroStarts N L).card : ℤ) ≤ (irregularStarts N L).card := by
    exact_mod_cast card_le_card (zeroStarts_subset_irregular hN hL)
  have ht : ((doubleStarts N L).card : ℤ) ≤ (irregularStarts N L).card := by
    exact_mod_cast card_le_card (doubleStarts_subset_irregular hN hL)
  rw [bias_count_identity N L hd]
  exact abs_le.mpr ⟨by omega, by omega⟩

theorem zero_double_disjoint (N L : ℕ) : Disjoint (zeroStarts N L) (doubleStarts N L) := by
  apply disjoint_left.mpr
  intro x hx hz
  have h₀ := (mem_filter.mp hx).2
  have h₂ := (mem_filter.mp hz).2
  omega

theorem irregular_partition {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hd : ∀ x ∈ dyadicBlock N, deficiency x L ≤ 1) :
    irregularStarts N L = zeroStarts N L ∪ doubleStarts N L := by
  ext x
  constructor
  · intro hx
    obtain ⟨hblock, hneq⟩ := mem_irregularStarts.mp hx
    have hxpos : 0 < x := by have h := (mem_Ico.mp hblock).1; omega
    have hrank := LocalRunRank.squareClass_rank_le x L hxpos
    have hdef := hd x hblock
    have hdefone : deficiency x L = 1 := by dsimp only [deficiency] at hdef ⊢; omega
    by_cases hpos : 0 < infiniteMarginal x L
    · apply mem_union_right
      apply mem_filter.mpr
      refine ⟨hblock, ?_⟩
      simp only [localMultiplicity, ite_eq_left hpos, hdefone, pow_one]
    · apply mem_union_left
      apply mem_filter.mpr
      exact ⟨hblock, by simp only [localMultiplicity, ite_eq_right hpos]⟩
  · intro hx
    rcases mem_union.mp hx with hz | ht
    · exact zeroStarts_subset_irregular hN hL hz
    · exact doubleStarts_subset_irregular hN hL ht

theorem irregular_card_partition {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hd : ∀ x ∈ dyadicBlock N, deficiency x L ≤ 1) :
    (irregularStarts N L).card = (zeroStarts N L).card + (doubleStarts N L).card := by
  rw [irregular_partition hN hL hd, card_union_of_disjoint (zero_double_disjoint N L)]

theorem bias_double_minus_irregular {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hd : ∀ x ∈ dyadicBlock N, deficiency x L ≤ 1) :
    bias (dyadicBlock N) L = 2 * ((doubleStarts N L).card : ℤ) - (irregularStarts N L).card := by
  have hcard : ((irregularStarts N L).card : ℤ) =
      (zeroStarts N L).card + (doubleStarts N L).card := by
    exact_mod_cast irregular_card_partition hN hL hd
  rw [bias_count_identity N L hd]
  omega

theorem bias_mod_two {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hd : ∀ x ∈ dyadicBlock N, deficiency x L ≤ 1) :
    bias (dyadicBlock N) L % 2 = ((irregularStarts N L).card : ℤ) % 2 := by
  have h := bias_double_minus_irregular hN hL hd
  omega

/-- A finite sufficient condition; no assertion is made that odd irregular
counts occur at infinitely many scales. -/
theorem bias_ne_zero_of_odd_irregular {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hd : ∀ x ∈ dyadicBlock N, deficiency x L ≤ 1) (hodd : Odd (irregularStarts N L).card) :
    bias (dyadicBlock N) L ≠ 0 := by
  have hbias := bias_double_minus_irregular hN hL hd
  rcases hodd with ⟨k, hk⟩
  omega

theorem uniform_critical_deficiency (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < L ∧ ∀ x ∈ dyadicBlock N, deficiency x L ≤ 1 := by
  obtain ⟨NR, hrank⟩ := RegularSetAsymptotic.dyadic_critical_relation_rank_le_one C
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 2 (max NR NG), by omega, ?_⟩
  intro N hN L hband
  have hNtwo : 2 ≤ N := by omega
  have hL : 0 < L := by have h := (hgeom N (by omega) L hband).2.2.1; omega
  have hd : ∀ x ∈ dyadicBlock N, deficiency x L ≤ 1 := by
    intro x hx
    have hxpos : 0 < x := by have h := (mem_Ico.mp hx).1; omega
    have hrel := hrank N (by omega) L hband x hx
    have hsum := LocalRunRank.squareClass_rank_add_relation_rank (L := L) hxpos
    dsimp only [deficiency]
    omega
  exact ⟨hL, hd⟩

theorem uniform_critical_classification (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      bias (dyadicBlock N) L = (doubleStarts N L).card - (zeroStarts N L).card ∧
        |bias (dyadicBlock N) L| ≤ (irregularStarts N L).card := by
  obtain ⟨N₀, hN₀, hdef⟩ := uniform_critical_deficiency C
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  obtain ⟨hL, hd⟩ := hdef N hN L hband
  exact ⟨bias_count_identity N L hd, abs_bias_le_irregular (by omega) hL hd⟩

theorem uniform_odd_irregular_mean (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → Odd (irregularStarts N L).card →
        countMoment (dyadicBlock N) L 1 ≠ (N : ℝ) * (2 ^ L : ℝ)⁻¹ := by
  obtain ⟨N₀, hN₀, hdef⟩ := uniform_critical_deficiency C
  refine ⟨N₀, ?_⟩
  intro N hN L hband hodd hmean
  obtain ⟨hL, hd⟩ := hdef N hN L hband
  have hbias := bias_ne_zero_of_odd_irregular (by omega : 2 ≤ N) hL hd hodd
  apply hbias
  apply (mean_eq_nominal_iff_bias_zero (by omega : 2 ≤ N) hL (subset_refl (dyadicBlock N))).mp
  simpa only [RegularSetFinite.card_dyadicBlock] using hmean

end PaperP1.MeanBiasClassification
