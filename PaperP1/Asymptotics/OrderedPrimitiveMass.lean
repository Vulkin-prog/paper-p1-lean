module

public import PaperP1.Asymptotics.PrimitiveNominalCountMass

/-! # Companion T4.3 at every fixed order at least four, including literal ordered nominal weights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrderedPrimitiveMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Probability PaperP1.ConnectedWindowFamilies

theorem subset_population {G : Finset ℕ} {L r : ℕ} (T : Finset (OrderedTuple G r))
    (hT : ∀ t ∈ T, Primitive L (tupleValues t)) :
    T ⊆ OrderedSubsetWeights.population G r (primitiveFamilies G L r) := by
  classical
  intro t ht
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨tupleValues_subset t, tupleValues_card t⟩, hT t ht⟩

theorem nominal_bound (r : ℕ) (hr : 2 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ G : Finset ℕ, ∀ T : Finset (OrderedTuple G r),
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → G ⊆ dyadicBlock N →
      (∀ t ∈ T, Primitive L (tupleValues t)) →
        (∑ t ∈ T, ((2 ^ L : ℝ)⁻¹) ^ r *
          (2 ^ relativeNullityOn (fun x ↦ squareClassSpace x L) (tupleValues t) : ℝ)) ≤
            (N : ℝ) ^ (1 - (r : ℝ) / 2 + ε) := by
  classical
  obtain ⟨NM, hNM⟩ := PrimitiveNominalCountMass.uniform_mass r hr C (ε / 2) (by positivity)
  obtain ⟨NF, hNF⟩ := HalfCountSchedule.factor_absorption (r.factorial : ℝ)
    (1 - (r : ℝ) / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max NM NF, ?_⟩
  intro N hN L G T hband hG hT
  have hsub : primitiveFamilies G L r ⊆ G.powersetCard r := filter_subset _ _
  calc
    _ ≤ ∑ t ∈ OrderedSubsetWeights.population G r (primitiveFamilies G L r),
        ((2 ^ L : ℝ)⁻¹) ^ r * (2 ^ relativeNullityOn (fun x ↦ squareClassSpace x L) (tupleValues t) : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (subset_population T hT) (fun t _ _ ↦ by positivity)
    _ = (r.factorial : ℝ) * PrimitiveNominalMass.mass (primitiveFamilies G L r) L :=
      PrimitiveNominalMass.ordered_sum G L r _ hsub
    _ ≤ (r.factorial : ℝ) * (N : ℝ) ^ (1 - (r : ℝ) / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_left (hNM N (by omega) L G hband hG) (Nat.cast_nonneg _)
    _ ≤ (N : ℝ) ^ (1 - (r : ℝ) / 2 + ε / 2 + ε / 2) := hNF N (by omega)
    _ = _ := by congr 1; ring

theorem actual_joint_bound (r : ℕ) (hr : 2 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ G : Finset ℕ, ∀ T : Finset (OrderedTuple G r),
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → G ⊆ dyadicBlock N →
      (∀ t ∈ T, Primitive L (tupleValues t)) →
        (∑ t ∈ T, infiniteJointMoment L (tupleValues t)) ≤ (N : ℝ) ^ (1 - (r : ℝ) / 2 + ε) := by
  classical
  obtain ⟨NM, hNM⟩ := PrimitiveGeneralMass.actual_joint_submass r hr C (ε / 2) (by positivity)
  obtain ⟨NF, hNF⟩ := HalfCountSchedule.factor_absorption (r.factorial : ℝ)
    (1 - (r : ℝ) / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max NM NF, ?_⟩
  intro N hN L G T hband hG hT
  have hsub : primitiveFamilies G L r ⊆ G.powersetCard r := filter_subset _ _
  calc
    _ ≤ ∑ t ∈ OrderedSubsetWeights.population G r (primitiveFamilies G L r), infiniteJointMoment L (tupleValues t) :=
      sum_le_sum_of_subset_of_nonneg (subset_population T hT) (fun t _ _ ↦ infiniteJointMoment_nonneg L _)
    _ = (r.factorial : ℝ) * ∑ I ∈ primitiveFamilies G L r, infiniteJointMoment L I :=
      OrderedSubsetWeights.weighted_sum G r _ hsub (infiniteJointMoment L)
    _ ≤ (r.factorial : ℝ) * (N : ℝ) ^ (1 - (r : ℝ) / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_left (hNM N (by omega) L G _ hband hG subset_rfl) (Nat.cast_nonneg _)
    _ ≤ (N : ℝ) ^ (1 - (r : ℝ) / 2 + ε / 2 + ε / 2) := hNF N (by omega)
    _ = _ := by congr 1; ring

theorem companion_T4_3_from_four (r : ℕ) (hr : 4 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ G : Finset ℕ, ∀ T : Finset (OrderedTuple G r),
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → G ⊆ dyadicBlock N →
      (∀ t ∈ T, Primitive L (tupleValues t)) →
        (∑ t ∈ T, ((2 ^ L : ℝ)⁻¹) ^ r *
          (2 ^ relativeNullityOn (fun x ↦ squareClassSpace x L) (tupleValues t) : ℝ)) ≤
            (N : ℝ) ^ (-(4 : ℝ) / 5 + ε) ∧
        (∑ t ∈ T, infiniteJointMoment L (tupleValues t)) ≤ (N : ℝ) ^ (-(4 : ℝ) / 5 + ε) := by
  obtain ⟨NN, hNN⟩ := nominal_bound r (by omega) C ε hε
  obtain ⟨NJ, hNJ⟩ := actual_joint_bound r (by omega) C ε hε
  refine ⟨max 1 (max NN NJ), ?_⟩
  intro N hN L G T hband hG hT
  have hpower : (N : ℝ) ^ (1 - (r : ℝ) / 2 + ε) ≤ (N : ℝ) ^ (-(4 : ℝ) / 5 + ε) := by
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
    have hrR : (4 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  exact ⟨(hNN N (by omega) L G T hband hG hT).trans hpower,
    (hNJ N (by omega) L G T hband hG hT).trans hpower⟩

end PaperP1.OrderedPrimitiveMass
