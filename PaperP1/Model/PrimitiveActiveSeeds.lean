module

public import PaperP1.Model.RetainedCountCylinder
public import PaperP1.Model.ConnectedWindowFamilies

/-! # A finite bad-event bound from minimal active dependencies and the actual mean -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveActiveSeeds

open Finset MeasureTheory PaperP1.Arithmetic PaperP1.Affine PaperP1.Algebra PaperP1.Probability
  PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.Model.InfiniteRademacher
  PaperP1.ConnectedWindowFamilies PaperP1.MaximumDirectActive PaperP1.RetainedActiveCount
  PaperP1.RetainedCountCylinder PaperP1.HeterogeneousDirectMaximum
  PaperP1.Probability.CylinderExpectations

local instance primitiveActiveSeedsDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def jointMass (G : Finset ℕ) (L r : ℕ) : ℝ :=
  ∑ I ∈ primitiveFamilies G L r, infiniteJointMoment L I

def activeWeight {Ω : Type*} (G : Finset ℕ) (L : ℕ) (J : ℕ → Ω → Bool) (ω : Ω) (r : ℕ) : ℝ :=
  ∑ I ∈ primitiveFamilies G L r, ∏ x ∈ I, (indicatorValue (J x ω) : ℝ)

theorem primitive_card_ge_two (L : ℕ) (I : Finset ℕ) (hI : Primitive L I) : 2 ≤ I.card := by
  by_contra h
  have hz := RetainedNullity.nullity_card_le_one (fun x ↦ squareClassSpace x L) I (by omega)
  exact (ne_of_gt hI.1) hz

theorem exists_primitive_subset (L : ℕ) (I : Finset ℕ) (hI : 0 < runRelativeNullity L I) :
    ∃ D ⊆ I, Primitive L D := by
  let F := I.powerset.filter fun D ↦ 0 < runRelativeNullity L D
  have hIF : I ∈ F := mem_filter.mpr ⟨mem_powerset.mpr (subset_refl I), hI⟩
  obtain ⟨D, hDF, hmin⟩ := exists_min_image F Finset.card ⟨I, hIF⟩
  obtain ⟨hDI, hpos⟩ := mem_filter.mp hDF
  refine ⟨D, mem_powerset.mp hDI, hpos, ?_⟩
  intro A hAD
  by_contra hzero
  have hAF : A ∈ F := mem_filter.mpr
    ⟨mem_powerset.mpr (hAD.subset.trans (mem_powerset.mp hDI)), Nat.pos_of_ne_zero hzero⟩
  have hle := hmin A hAF
  have hlt := card_lt_card hAD
  omega

theorem not_retained_positive (H : ℝ) (N L : ℕ) (I : Finset ℕ)
    (hI : ¬ RetainedGoodEdges.Retained H N L I) : 0 < runRelativeNullity L I := by
  apply Nat.pos_of_ne_zero
  intro hz
  exact hI ((CompressedBlocks.sourceRetained_iff (fun x ↦ squareClassSpace x L)
    (GoodEdgeCompression.goodEdges H N L) I).mpr (Or.inl hz))

theorem activeWeight_nonneg {Ω : Type*} (G : Finset ℕ) (L : ℕ) (J : ℕ → Ω → Bool) (ω : Ω) (r : ℕ) :
    0 ≤ activeWeight G L J ω r := sum_nonneg fun I _ ↦ indicator_product_nonneg J I ω

theorem bad_indicator_bound {Ω : Type*} (H : ℝ) (N L : ℕ) (G : Finset ℕ)
    (J : ℕ → Ω → Bool) (ω : Ω) (K : ℕ) :
    (if ¬ RetainedGoodEdges.Retained H N L (activeSites G J ω) then (1 : ℝ) else 0) ≤
      (indicatorCount G J ω : ℝ) / (K + 1 : ℕ) + ∑ r ∈ Icc 2 K, activeWeight G L J ω r := by
  have hf : 0 ≤ (indicatorCount G J ω : ℝ) / (K + 1 : ℕ) := by positivity
  have hs : 0 ≤ ∑ r ∈ Icc 2 K, activeWeight G L J ω r :=
    sum_nonneg fun r _ ↦ activeWeight_nonneg G L J ω r
  by_cases hret : RetainedGoodEdges.Retained H N L (activeSites G J ω)
  · simp only [hret, not_true_eq_false, ite_false]
    linarith only [hf, hs]
  · simp only [hret, not_false_eq_true, ite_true]
    by_cases hlarge : K < indicatorCount G J ω
    · have hcount : ((K + 1 : ℕ) : ℝ) ≤ indicatorCount G J ω := by exact_mod_cast (show K + 1 ≤ indicatorCount G J ω by omega)
      have hone : (1 : ℝ) ≤ (indicatorCount G J ω : ℝ) / (K + 1 : ℕ) :=
        (le_div_iff₀ (by positivity : (0 : ℝ) < (K + 1 : ℕ))).mpr (by simpa only [one_mul] using hcount)
      linarith only [hone, hs]
    · obtain ⟨D, hDA, hprim⟩ := exists_primitive_subset L (activeSites G J ω) (not_retained_positive H N L _ hret)
      have hDG : D ⊆ G := hDA.trans (filter_subset _ _)
      have hrlo := primitive_card_ge_two L D hprim
      have hrhi : D.card ≤ K := by
        have h := card_le_card hDA
        rw [card_activeSites] at h
        omega
      have hD : D ∈ primitiveFamilies G L D.card := mem_filter.mpr
        ⟨mem_powersetCard.mpr ⟨hDG, rfl⟩, hprim⟩
      have hact : ∀ x ∈ D, J x ω = true := fun x hx ↦ (mem_filter.mp (hDA hx)).2
      have hp : (∏ x ∈ D, (indicatorValue (J x ω) : ℝ)) = 1 := by
        rw [indicator_product_eq_indicator, ite_eq_left hact]
      have hinner : (1 : ℝ) ≤ activeWeight G L J ω D.card := by
        simpa only [activeWeight, hp] using single_le_sum (fun I _ ↦ indicator_product_nonneg J I ω) hD
      have houter : activeWeight G L J ω D.card ≤ ∑ r ∈ Icc 2 K, activeWeight G L J ω r :=
        single_le_sum (fun r _ ↦ activeWeight_nonneg G L J ω r) (mem_Icc.mpr ⟨hrlo, hrhi⟩)
      linarith only [hinner, houter, hf]

theorem finite_activeWeight_expectation (G : Finset ℕ) (L r : ℕ) :
    finiteExpectation (cylinderProbability (cutoff G L)).weight
      (fun σ ↦ activeWeight G L (fun x ↦ startIndicator x L) σ r) = jointMass G L r := by
  unfold activeWeight jointMass
  rw [finiteExpectation_sum]
  apply sum_congr rfl
  intro I hI
  have hIG := (mem_powersetCard.mp (mem_filter.mp hI).1).1
  exact (infiniteJointMoment_eq_finite (cutoff G L) L I
    (fun x hx ↦ le_sup (f := fun x ↦ x + L) (hIG hx))).symm

theorem finite_count_mean (G : Finset ℕ) (L : ℕ) :
    finiteExpectation (cylinderProbability (cutoff G L)).weight
      (fun σ ↦ (indicatorCount G (fun x ↦ startIndicator x L) σ : ℝ)) = actualMean G L := by
  rw [mean_indicatorCount]
  apply sum_congr rfl
  intro x hx
  exact (infiniteMarginal_eq_finite (le_sup (f := fun x ↦ x + L) hx)).symm

theorem badProbability_bound (H : ℝ) (N L : ℕ) (G : Finset ℕ) (K : ℕ) :
    badProbability H N L G ≤ actualMean G L / (K + 1 : ℕ) + ∑ r ∈ Icc 2 K, jointMass G L r := by
  have hcut (x : ℕ) (hx : x ∈ G) : x + L ≤ cutoff G L := le_sup (f := fun x ↦ x + L) hx
  have hb : badProbability H N L G = finiteExpectation (cylinderProbability (cutoff G L)).weight
      (fun σ ↦ if ¬ finiteRetained H N L G σ then (1 : ℝ) else 0) := by
    rw [← infiniteCylinder_event (cutoff G L) (fun σ ↦ ¬ finiteRetained H N L G σ)]
    unfold badProbability
    congr 1
    ext ω
    exact (not_congr (finite_retained_restrict H N L G hcut ω)).symm
  rw [hb]
  have hm := finiteExpectation_mono (cylinderProbability (cutoff G L))
    (fun σ ↦ bad_indicator_bound H N L G (fun x ↦ startIndicator x L) σ K)
  rw [finiteExpectation_add, finiteExpectation_sum] at hm
  have hmean : finiteExpectation (cylinderProbability (cutoff G L)).weight
      (fun σ ↦ (indicatorCount G (fun x ↦ startIndicator x L) σ : ℝ) / (K + 1 : ℕ)) =
      actualMean G L / (K + 1 : ℕ) := by
    simp only [div_eq_mul_inv]
    rw [finiteExpectation_mul_const, finite_count_mean]
  rw [hmean] at hm
  simp only [finite_activeWeight_expectation] at hm
  convert hm using 1
  congr 1

end PaperP1.PrimitiveActiveSeeds
