module

public import PaperP1.Asymptotics.IsolatedVertexTripleMass
public import PaperP1.Asymptotics.CoarseTriplePairSeedBounds
public import PaperP1.Asymptotics.CoarseTripleFiniteReduction
public import PaperP1.Asymptotics.SharedFiniteInteriorTripleMass

/-! # The entire actual connected triple joint mass has coarse rate1 without unproved geometric inputs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoarseConnectedTripleMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies

theorem uniform_mass (C ε : ℝ) (hε : 0 < ε) :
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
        F ⊆ connectedFamilies G L 3 →
        (∑ T ∈ F, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨Q, _hQ, hcover⟩ := CoarseTripleFiniteReduction.uniform_cover (ε / 4) (by positivity)
  obtain ⟨NC, _hNC, hc⟩ := hcover C
  obtain ⟨NI, _hNI, hi⟩ := IsolatedVertexTripleMass.uniform_mass C (ε / 2) (by positivity)
  obtain ⟨NB, _hNB, hb⟩ := CoarseTriplePairSeedBounds.uniform_extensions 1 (ε / 4) C (ε / 4)
    (by positivity) (by positivity)
  obtain ⟨NA, _hNA, ha⟩ := SharedFiniteInteriorTripleMass.uniform_mass Q C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 3 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NC + NI + NB + NA + NF, by omega, ?_⟩
  intro N hN L hband G hG F hF
  let I := fun T : Finset ℕ ↦ ∃ x ∈ T, ∀ y ∈ T.erase x,
    Disjoint (squareClassSpace x L) (squareClassSpace y L)
  let B := fun T : Finset ℕ ↦ ∃ e ∈ CoarseTriplePairSeeds.pairs N L (ε / 4), e ⊆ T
  let A := fun T : Finset ℕ ↦
    2 ≤ ((FiniteInteriorUnitEdges.edges N L Q).filter fun e ↦ e ⊆ T).card
  let FI := F.filter I
  let FB := F.filter B
  let FA := F.filter A
  have hdata (T : Finset ℕ) (hT : T ∈ F) : T ⊆ dyadicBlock N ∧ T.card = 3 := by
    obtain ⟨hTG, hcard⟩ := mem_powersetCard.mp (mem_filter.mp (hF hT)).1
    exact ⟨hTG.trans hG, hcard⟩
  have hsub : F ⊆ (FI ∪ FB) ∪ FA := by
    intro T hT
    have h := hc N (by omega) L hband T (hdata T hT).1 (hdata T hT).2
    rcases h with hI | hB | hA
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hT, hI⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hT, hB⟩))
    · exact mem_union_right _ (mem_filter.mpr ⟨hT, hA⟩)
  have hI : (∑ T ∈ FI, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-1 + ε / 2) :=
    hi N (by omega) L hband G hG FI (filter_subset _ _ |>.trans hF)
      (fun _ hT ↦ (mem_filter.mp hT).2)
  have hB : (∑ T ∈ FB, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-1 + ε / 2) := by
    convert hb N (by omega) L hband FB (fun T hT ↦
      ⟨(hdata T (mem_filter.mp hT).1).1, (hdata T (mem_filter.mp hT).1).2, (mem_filter.mp hT).2⟩) using 1
    congr 1
    ring
  have hA : (∑ T ∈ FA, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-1 + ε / 2) := by
    apply (ha N (by omega) L hband FA (fun T hT ↦
      ⟨(hdata T (mem_filter.mp hT).1).1, (hdata T (mem_filter.mp hT).1).2, (mem_filter.mp hT).2⟩)).trans
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only [])
  have h0 := sum_le_sum_of_subset_of_nonneg hsub (fun T _ _ ↦ infiniteJointMoment_nonneg L T)
  have h1 := GraphStarWeights.sum_union_le_nonneg FI FB (infiniteJointMoment L) (infiniteJointMoment_nonneg L)
  have h2 := GraphStarWeights.sum_union_le_nonneg (FI ∪ FB) FA (infiniteJointMoment L) (infiniteJointMoment_nonneg L)
  have hfactor : 3 * (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  linarith only [hI, hB, hA, h0, h1, h2, hfactor]

end PaperP1.CoarseConnectedTripleMass
