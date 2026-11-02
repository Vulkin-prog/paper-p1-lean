module

public import PaperP1.Model.PrivateNormalizedFamilyRank
public import PaperP1.Arithmetic.ThreeSlopeValueCounts
public import PaperP1.Model.TripleProbabilityBound

/-! # Exact actual joint probabilities of the extremal rational witness and its three pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ThreeSlopeWitnessMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ThreeSlopeProgressions PaperP1.ThreeSlopeValueCounts PaperP1.NormalizedWindowSets
  PaperP1.PrivateNormalizedFamilies PaperP1.PrivateNormalizedFamilyRank

def support (t : ℕ) : Finset ℕ := FiniteFamilyEnumeration.tupleSet (centres t)

theorem centres_injective {t : ℕ} (ht : 1 ≤ t) : Function.Injective (centres t) := by
  intro i j hh
  fin_cases i <;> fin_cases j <;> norm_num [centres, multiple] at * <;> omega

theorem support_eq (t : ℕ) : support t = {10 * t, 12 * t, 15 * t} := by
  have hu : (univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  rw [support, FiniteFamilyEnumeration.tupleSet, hu]
  simp only [image_insert, image_singleton]
  rfl

theorem support_card {t : ℕ} (ht : 1 ≤ t) : (support t).card = 3 := by
  rw [support, FiniteFamilyEnumeration.tupleSet, card_image_of_injective _ (centres_injective ht), card_univ, Fintype.card_fin]

theorem marginals {t L : ℕ} (ht : 1 ≤ t) (hL : 1 ≤ L)
    (hprivate : FiniteEvenSquareClasses.Private (valueUnion step (centres t) L)) :
    ∀ i, infiniteMarginal (centres t i) L = (2 ^ L : ℝ)⁻¹ := by
  intro i
  exact TripleProbabilityBound.marginal_of_full_rank (by have hh := centres_ge_two ht i; omega) (by omega)
    (local_ranks step (centres t) step_pos (centres_ge_two ht) hprivate i)

theorem joint_probability {t L : ℕ} (ht : 1 ≤ t) (hL : 1 ≤ L)
    (hprivate : FiniteEvenSquareClasses.Private (valueUnion step (centres t) L)) :
    infiniteJointMoment L (support t) = ((2 ^ L : ℝ)⁻¹) ^ 3 * (2 ^ nullity L : ℝ) := by
  exact probability_nullity (by omega) step (centres t) step_pos (centres_ge_two ht) (by omega)
    (60 * t) (common_mem ht (by omega)) hprivate (exclusive ht L) (nullity L) (nullity_rank_identity ht hL)

theorem pair_probability {t L : ℕ} (ht : 1 ≤ t) (hL : 1 ≤ L)
    (hprivate : FiniteEvenSquareClasses.Private (valueUnion step (centres t) L))
    (i j : Fin 3) (d : ℕ)
    (hinter : (normalized (step i) (centres t i) L ∩ normalized (step j) (centres t j) L).card = pairFloor L d + 1) :
    infiniteJointMoment L {centres t i, centres t j} = ((2 ^ L : ℝ)⁻¹) ^ 2 * (2 ^ pairFloor L d : ℝ) := by
  let e : Fin 2 → Fin 3 := ![i, j]
  let c₂ : Fin 2 → ℕ := fun a ↦ step (e a)
  let X₂ : Fin 2 → ℕ := fun a ↦ centres t (e a)
  have hu : (univ : Finset (Fin 2)) = {0, 1} := by decide
  have hUnion : valueUnion c₂ X₂ L = normalized (step i) (centres t i) L ∪ normalized (step j) (centres t j) L := by
    rw [valueUnion, hu]
    simp only [biUnion_insert, singleton_biUnion]
    rfl
  have hSupport : FiniteFamilyEnumeration.tupleSet X₂ = {centres t i, centres t j} := by
    rw [FiniteFamilyEnumeration.tupleSet, hu]
    simp only [image_insert, image_singleton]
    rfl
  have hpriv₂ : FiniteEvenSquareClasses.Private (valueUnion c₂ X₂ L) := by
    rw [hUnion]
    exact hprivate.mono (union_subset (normalized_subset step (centres t) L i) (normalized_subset step (centres t) L j))
  have hcard := card_union_add_card_inter (normalized (step i) (centres t i) L) (normalized (step j) (centres t j) L)
  rw [card_normalized (step_pos i) (by have hh := centres_ge_two ht i; omega),
    card_normalized (step_pos j) (by have hh := centres_ge_two ht j; omega), hinter] at hcard
  have hnon : 1 ≤ (valueUnion c₂ X₂ L).card := by
    apply card_pos.mpr
    rw [hUnion]
    exact (normalized_nonempty (step i) (centres t i) L).mono subset_union_left
  have hdim : (valueUnion c₂ X₂ L).card - 1 + pairFloor L d = 2 * L := by rw [hUnion] at *; omega
  have hh := probability_nullity (by omega : 0 < 2) c₂ X₂
    (fun a ↦ step_pos (e a)) (fun a ↦ centres_ge_two ht (e a)) (by omega)
    (60 * t) (fun a ↦ common_mem ht (by omega) (e a)) hpriv₂
    (fun a b u ↦ exclusive ht L (e a) (e b) u) (pairFloor L d) hdim
  rwa [hSupport] at hh

theorem pair_zero_one_probability {t L : ℕ} (ht : 1 ≤ t) (hL : 1 ≤ L)
    (hprivate : FiniteEvenSquareClasses.Private (valueUnion step (centres t) L)) :
    infiniteJointMoment L {centres t 0, centres t 1} = ((2 ^ L : ℝ)⁻¹) ^ 2 * (2 ^ pairFloor L 6 : ℝ) :=
  pair_probability ht hL hprivate 0 1 6 (pair_zero_one ht hL)

theorem pair_zero_two_probability {t L : ℕ} (ht : 1 ≤ t) (hL : 1 ≤ L)
    (hprivate : FiniteEvenSquareClasses.Private (valueUnion step (centres t) L)) :
    infiniteJointMoment L {centres t 0, centres t 2} = ((2 ^ L : ℝ)⁻¹) ^ 2 * (2 ^ pairFloor L 3 : ℝ) :=
  pair_probability ht hL hprivate 0 2 3 (pair_zero_two ht hL)

theorem pair_one_two_probability {t L : ℕ} (ht : 1 ≤ t) (hL : 1 ≤ L)
    (hprivate : FiniteEvenSquareClasses.Private (valueUnion step (centres t) L)) :
    infiniteJointMoment L {centres t 1, centres t 2} = ((2 ^ L : ℝ)⁻¹) ^ 2 * (2 ^ pairFloor L 5 : ℝ) :=
  pair_probability ht hL hprivate 1 2 5 (pair_one_two ht hL)

end PaperP1.ThreeSlopeWitnessMass
