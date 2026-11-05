module

public import PaperP1.Asymptotics.SmallCoreSourceMass
public import PaperP1.Asymptotics.LargeCoreClosureMass
public import PaperP1.Asymptotics.LowCompatibleNullityTail
public import PaperP1.Asymptotics.Primitive256Tail

/-! # The entire connected clause of article15.12 has the stronger power83/60 without unproved inputs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedTail

open Finset Filter PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies

theorem uniform_tail (K : ℕ → ℕ)
    (hK : Tendsto (fun N : ℕ ↦ (K N : ℝ) / Real.log N) atTop (nhds 0))
    (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ G ∧ Connected L I ∧ 256 < I.card ∧ I.card ≤ K N ∧ runCompatibleNullity L I ≤ 2 * L) →
        (∑ I ∈ F, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-83 / 60 + ε) := by
  classical
  obtain ⟨NS, _hNS, hs⟩ := SmallCoreSourceMass.uniform_families K hK
    u C (ε / 2) hu (by positivity)
  obtain ⟨NL, _hNL, hl⟩ := LowCompatibleNullityTail.uniform_bound u C (ε / 2) hu (by positivity)
  obtain ⟨NC, _hNC, hc⟩ := LargeCoreClosureMass.uniform_bound u C (ε / 2) hu (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 3 (-83 / 60 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NS + NL + NC + NF, by omega, ?_⟩
  intro N hN L hband G hG F hF
  let Low := fun I : Finset ℕ ↦ (runCompatibleNullity L I : ℝ) ≤ (L : ℝ) / 60
  let Large := fun I : Finset ℕ ↦ 256 ≤ (ChosenRelationCore.core L I).card
  let FL := F.filter Low
  let FC := F.filter Large
  let FS := F.filter fun I ↦ ¬ Low I ∧ ¬ Large I
  let w := fun I : Finset ℕ ↦ u ^ I.card * |infiniteCenteredCoefficient L I|
  have hw (I : Finset ℕ) : 0 ≤ w I := mul_nonneg (pow_nonneg hu.le _) (abs_nonneg _)
  have hcover : F ⊆ (FL ∪ FC) ∪ FS := by
    intro I hI
    by_cases hlow : Low I
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hI, hlow⟩))
    by_cases hlarge : Large I
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hI, hlarge⟩))
    exact mem_union_right _ (mem_filter.mpr ⟨hI, hlow, hlarge⟩)
  have hlow : (∑ I ∈ FL, w I) ≤ (N : ℝ) ^ (-83 / 60 + ε / 2) := by
    apply hl N (by omega) L hband FL
    intro I hI
    obtain ⟨hIF, hlow⟩ := mem_filter.mp hI
    obtain ⟨hIG, hconn, hlarge, _hsize, _hnull⟩ := hF I hIF
    exact ⟨hIG.trans hG, by omega, hconn, hlow⟩
  have hpower : (N : ℝ) ^ (-3 / 2 + ε / 2) ≤ (N : ℝ) ^ (-83 / 60 + ε / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only [])
  have hlarge : (∑ I ∈ FC, w I) ≤ (N : ℝ) ^ (-83 / 60 + ε / 2) := by
    apply (hc N (by omega) L hband G hG FC ?_).trans hpower
    intro I hI
    obtain ⟨hIF, hlarge⟩ := mem_filter.mp hI
    have hd := hF I hIF
    exact ⟨hd.1, hlarge, hd.2.2.2.2⟩
  have hsmall : (∑ I ∈ FS, w I) ≤ (N : ℝ) ^ (-83 / 60 + ε / 2) := by
    apply (hs N (by omega) L hband G hG FS ?_).trans hpower
    intro I hI
    obtain ⟨hIF, hnotLow, hnotLarge⟩ := mem_filter.mp hI
    obtain ⟨hIG, hconn, hlarge, hsize, _hnull⟩ := hF I hIF
    exact ⟨hIG, hconn, hlarge, hsize, lt_of_not_ge hnotLow, Nat.lt_of_not_ge hnotLarge⟩
  have h0 := sum_le_sum_of_subset_of_nonneg hcover (fun I _ _ ↦ hw I)
  have h1 := GraphStarWeights.sum_union_le_nonneg FL FC w hw
  have h2 := GraphStarWeights.sum_union_le_nonneg (FL ∪ FC) FS w hw
  have hfactor : 3 * (N : ℝ) ^ (-83 / 60 + ε / 2) ≤ (N : ℝ) ^ (-83 / 60 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  linarith only [hlow, hlarge, hsmall, h0, h1, h2, hfactor]

theorem article_15_12 (K : ℕ → ℕ)
    (hK : Tendsto (fun N : ℕ ↦ (K N : ℝ) / Real.log N) atTop (nhds 0))
    (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        ((∀ F : Finset (Finset ℕ),
          (∀ I ∈ F, I ⊆ G ∧ Connected L I ∧ 256 < I.card ∧ I.card ≤ K N ∧ runCompatibleNullity L I ≤ 2 * L) →
          (∑ I ∈ F, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-4 / 3 + ε)) ∧
        (∑ I ∈ WeightedPrimitiveMass.families G L 257, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤
          (N : ℝ) ^ (-4 / 3 + ε)) := by
  obtain ⟨NC, _hNC, hc⟩ := uniform_tail K hK u C ε hu hε
  obtain ⟨NP, _hNP, hp⟩ := Primitive256Tail.article_15_12_primitive u C ε hu hε
  refine ⟨10 + NC + NP, by omega, ?_⟩
  intro N hN L hband G hG
  refine ⟨?_, hp N (by omega) L hband G hG⟩
  intro F hF
  exact (hc N (by omega) L hband G hG F hF).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only []))

end PaperP1.ConnectedTail
