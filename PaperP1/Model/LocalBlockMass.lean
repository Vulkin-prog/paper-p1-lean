module

public import PaperP1.Model.LocalBlockGeometry
public import PaperP1.Model.CountObservables
public import PaperP1.Probability.BernoulliCount

/-! # Exact Bernoulli block laws and the signed and absolute local mean discrepancies -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalBlockMass

open MeasureTheory Finset PaperP1.LocalRelationSets PaperP1.LocalRelationBlocks PaperP1.LocalBlockGeometry
  PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.Probability
  PaperP1.RegularStarts PaperP1.CountObservables PaperP1.WindowRelationCode

def endpointCount (N : ℕ) (S : Finset ℕ) : ℕ := if first S + 1 ∈ dyadicBlock N then 1 else 0

def blockParameter (N L : ℕ) (S : Finset ℕ) : ℝ :=
  2 * (2 ^ L : ℝ)⁻¹ * ((block N L S).card - (endpointCount N S : ℝ))

theorem blockParameter_eq_nat {N L : ℕ} {S : Finset ℕ} (hS : S ∈ relations N L) :
    blockParameter N L S = 2 * (2 ^ L : ℝ)⁻¹ * ((block N L S).card - endpointCount N S : ℕ) := by
  have hpos := card_pos.mpr (block_nonempty hS)
  have hendpoint : endpointCount N S ≤ 1 := by unfold endpointCount; split_ifs <;> omega
  rw [blockParameter, Nat.cast_sub (by omega : endpointCount N S ≤ (block N L S).card)]

theorem endpoint_mem_block_iff {N L : ℕ} (hN : 2 ≤ N) {S : Finset ℕ} (hS : S ∈ relations N L) :
    first S + 1 ∈ block N L S ↔ first S + 1 ∈ dyadicBlock N := by
  constructor
  · exact fun h ↦ ((mem_block N L S _).mp h).1
  · intro hbox
    obtain ⟨hrel, x, hx, hwin⟩ := (mem_relations N L S).mp hS
    have hxpos : 0 < x := by have h := (mem_Ico.mp hx).1; omega
    obtain ⟨hlo, hhi⟩ := (subset_window_iff hxpos S hrel.1).mp hwin
    apply (mem_block N L S _).mpr
    exact ⟨hbox, (subset_window_iff (by omega) S hrel.1).mpr ⟨le_rfl, by omega⟩⟩

theorem block_marginal_sum {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hrank : ∀ x ∈ dyadicBlock N, Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1)
    {S : Finset ℕ} (hS : S ∈ relations N L) :
    (∑ x ∈ block N L S, infiniteMarginal x L) = blockParameter N L S := by
  classical
  have hpoint (x : ℕ) (hx : x ∈ block N L S) :
      infiniteMarginal x L = 2 * (2 ^ L : ℝ)⁻¹ - if x = first S + 1 then 2 * (2 ^ L : ℝ)⁻¹ else 0 := by
    rw [block_marginal hN hL hrank hS hx]
    split_ifs <;> ring
  rw [sum_congr rfl hpoint, sum_sub_distrib]
  simp only [sum_const, nsmul_eq_mul, sum_ite_eq', endpoint_mem_block_iff hN hS]
  unfold blockParameter endpointCount
  split_ifs <;> push_cast <;> ring

theorem block_law {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hrank : ∀ x ∈ dyadicBlock N, Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1)
    {S : Finset ℕ} (hS : S ∈ relations N L) :
    restrictedCountLaw N L (block N L S) = bernoulli (blockParameter N L S) := by
  unfold restrictedCountLaw
  rw [countLaw_eq_bernoulli _ _ _ (finiteCount_le_one ((mem_relations N L S).mp hS).1)]
  congr 1
  calc
    _ = ∑ x ∈ block N L S, infiniteMarginal x L := by
      apply sum_congr rfl
      intro x hx
      exact (infiniteMarginal_eq_finite (dyadic_subset_cutoff (filter_subset _ _) x hx)).symm
    _ = _ := block_marginal_sum hN hL hrank hS

theorem blockParameter_mem_unit_interval {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hrank : ∀ x ∈ dyadicBlock N, Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1)
    {S : Finset ℕ} (hS : S ∈ relations N L) : 0 ≤ blockParameter N L S ∧ blockParameter N L S ≤ 1 := by
  have hprob := restrictedCountLaw_isProbability N L (block N L S)
  rw [block_law hN hL hrank hS] at hprob
  have hzero := hprob.1 0
  have hone := hprob.1 1
  norm_num [bernoulli_coeff] at hzero hone
  exact ⟨hone, by linarith⟩

theorem block_law_realizes {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hrank : ∀ x ∈ dyadicBlock N, Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1)
    {S : Finset ℕ} (hS : S ∈ relations N L) :
    lawMeasure (bernoulli (blockParameter N L S))
      (bernoulli_isProbability (blockParameter_mem_unit_interval hN hL hrank hS).1
        (blockParameter_mem_unit_interval hN hL hrank hS).2).1 =
      InfiniteRademacher.infiniteRademacherMeasure.map (infiniteStartCount (block N L S) L) := by
  have h := restrictedCountLaw_realizes (N := N) (L := L) (G := block N L S) (filter_subset _ _)
  simpa only [block_law hN hL hrank hS] using h

theorem outside_marginal {N L x : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (hx : x ∈ dyadicBlock N)
    (hout : x ∉ irregularStarts N L) : infiniteMarginal x L = (2 ^ L : ℝ)⁻¹ := by
  have hxpos : 0 < x := by have h := (mem_Ico.mp hx).1; omega
  have hfull : Module.finrank F₂ (squareClassSpace x L) = L := by
    by_contra hnot
    exact hout (mem_irregularStarts.mpr ⟨hx, hnot⟩)
  exact marginal_on_regular hxpos hL (mem_regularStarts.mpr ⟨hx, hfull⟩)

theorem sum_over_blocks {N L : ℕ} (hN : 2 ≤ N)
    (hrank : ∀ x ∈ dyadicBlock N, Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1)
    (f : ℕ → ℝ) (hf : ∀ x ∈ dyadicBlock N, x ∉ irregularStarts N L → f x = 0) :
    (∑ x ∈ dyadicBlock N, f x) = ∑ S ∈ relations N L, ∑ x ∈ block N L S, f x := by
  classical
  calc
    _ = ∑ x ∈ irregularStarts N L, f x := (sum_subset sdiff_subset hf).symm
    _ = _ := by
      rw [← blocks_cover_irregular hN]
      exact sum_biUnion (fun S hS T hT hne ↦ blocks_disjoint hN hrank hS hT hne)

theorem block_signed_discrepancy {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hrank : ∀ x ∈ dyadicBlock N, Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1)
    {S : Finset ℕ} (hS : S ∈ relations N L) :
    (∑ x ∈ block N L S, (infiniteMarginal x L - (2 ^ L : ℝ)⁻¹)) =
      (2 ^ L : ℝ)⁻¹ * ((block N L S).card - 2 * (endpointCount N S : ℝ)) := by
  rw [sum_sub_distrib, block_marginal_sum hN hL hrank hS]
  simp only [sum_const, nsmul_eq_mul, blockParameter]
  ring

theorem block_absolute_discrepancy {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hrank : ∀ x ∈ dyadicBlock N, Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1)
    {S : Finset ℕ} (hS : S ∈ relations N L) :
    (∑ x ∈ block N L S, |infiniteMarginal x L - (2 ^ L : ℝ)⁻¹|) =
      (2 ^ L : ℝ)⁻¹ * (block N L S).card := by
  have hpoint (x : ℕ) (hx : x ∈ block N L S) : |infiniteMarginal x L - (2 ^ L : ℝ)⁻¹| = (2 ^ L : ℝ)⁻¹ := by
    rw [block_marginal hN hL hrank hS hx]
    by_cases heq : x = first S + 1
    · rw [ite_eq_left heq, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
    · rw [ite_eq_right heq, show 2 * (2 ^ L : ℝ)⁻¹ - (2 ^ L : ℝ)⁻¹ = (2 ^ L : ℝ)⁻¹ by ring,
        abs_of_nonneg (by positivity)]
  rw [sum_congr rfl hpoint]
  simp only [sum_const, nsmul_eq_mul, mul_comm]

theorem mean_discrepancy {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hrank : ∀ x ∈ dyadicBlock N, Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1) :
    countMoment (dyadicBlock N) L 1 - N * (2 ^ L : ℝ)⁻¹ =
      (2 ^ L : ℝ)⁻¹ * ∑ S ∈ relations N L, ((block N L S).card - 2 * (endpointCount N S : ℝ)) := by
  rw [countMoment_one (subset_refl _)]
  calc
    _ = ∑ x ∈ dyadicBlock N, (infiniteMarginal x L - (2 ^ L : ℝ)⁻¹) := by
      rw [sum_sub_distrib]
      simp only [sum_const, nsmul_eq_mul, dyadicBlock_card]
    _ = ∑ S ∈ relations N L, ∑ x ∈ block N L S, (infiniteMarginal x L - (2 ^ L : ℝ)⁻¹) := by
      apply sum_over_blocks hN hrank
      intro x hx hout
      rw [outside_marginal hN hL hx hout, sub_self]
    _ = _ := by
      rw [mul_sum]
      exact sum_congr rfl (fun S hS ↦ block_signed_discrepancy hN hL hrank hS)

theorem absolute_discrepancy {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hrank : ∀ x ∈ dyadicBlock N, Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1) :
    (∑ x ∈ dyadicBlock N, |infiniteMarginal x L - (2 ^ L : ℝ)⁻¹|) =
      (2 ^ L : ℝ)⁻¹ * ∑ S ∈ relations N L, ((block N L S).card : ℝ) := by
  calc
    _ = ∑ S ∈ relations N L, ∑ x ∈ block N L S, |infiniteMarginal x L - (2 ^ L : ℝ)⁻¹| := by
      apply sum_over_blocks hN hrank
      intro x hx hout
      rw [outside_marginal hN hL hx hout, sub_self, abs_zero]
    _ = _ := by
      rw [mul_sum]
      exact sum_congr rfl (fun S hS ↦ block_absolute_discrepancy hN hL hrank hS)

end PaperP1.LocalBlockMass
