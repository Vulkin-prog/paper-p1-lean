module

public import PaperP1.Model.RetainedReferenceTheorem

/-! # The literal cardinality coefficients F_r, G_r and admitted compressed extensions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedCardinalityDeficits

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Probability PaperP1.Model
  PaperP1.Model.InfiniteStarts PaperP1.RegularStarts PaperP1.GoodEdgeCompression
  PaperP1.RetainedGoodEdges PaperP1.RetainedReferenceIdentity PaperP1.RetainedReferenceTheorem

local instance (P : Prop) : Decidable P := Classical.propDecidable P
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def excluded (N L : ℕ) : Finset (Finset ℕ) :=
  (regularStarts N L).powerset.filter (fun I ↦ runRelativeNullity L I ≠ 0)

def directAt (N L r : ℕ) : Finset (Finset ℕ) := by
  classical
  exact ((regularStarts N L).powersetCard r).filter (fun I ↦ runRelativeNullity L I = 0)

def gamma (N L : ℕ) (e : Finset ℕ) (h : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (((regularStarts N L) \ e).powersetCard h).filter
    (fun A ↦ RetainedDependence.Compressed (fun x ↦ squareClassSpace x L) e (e ∪ A))

def firstCoefficient (N L r : ℕ) : ℝ :=
  ((2 ^ L : ℝ)⁻¹) ^ r * (((regularStarts N L).card.choose r - (directAt N L r).card : ℕ) : ℝ)

def edgeCoefficient (N L : ℕ) (e : Finset ℕ) (r : ℕ) : ℝ :=
  if r < 2 then 0 else infiniteJointMoment L e * ((2 ^ L : ℝ)⁻¹) ^ (r - 2) *
    ((((regularStarts N L).card - 2).choose (r - 2) - (gamma N L e (r - 2)).card : ℕ) : ℝ)

def secondCoefficient (H : ℝ) (N L r : ℕ) : ℝ :=
  ∑ e ∈ goodEdges H N L, edgeCoefficient N L e r

theorem sum_by_shifted_card {R : Type*} [AddCommMonoid R] (F : Finset (Finset ℕ))
    (n k : ℕ) (hsize : ∀ A ∈ F, A.card + k ≤ n) (f : Finset ℕ → R) :
    (∑ A ∈ F, f A) = ∑ r ∈ range (n + 1), ∑ A ∈ F.filter (fun A ↦ A.card + k = r), f A := by
  exact (sum_fiberwise_of_maps_to (t := range (n + 1)) (g := fun A : Finset ℕ ↦ A.card + k)
    (fun A hA ↦ mem_range.mpr (by have h := hsize A hA; omega)) f).symm

theorem first_layer_eq (N L r : ℕ) :
    ((regularStarts N L).powerset.filter (fun I ↦ runRelativeNullity L I ≠ 0)).filter
      (fun I ↦ I.card = r) = ((regularStarts N L).powersetCard r).filter
        (fun I ↦ runRelativeNullity L I ≠ 0) := by
  classical
  ext I
  simp only [mem_filter, mem_powerset, mem_powersetCard]
  tauto

theorem first_layer_count (N L r : ℕ) :
    (((regularStarts N L).powersetCard r).filter (fun I ↦ runRelativeNullity L I ≠ 0)).card =
      (regularStarts N L).card.choose r - (directAt N L r).card := by
  classical
  have h := card_filter_add_card_filter_not (s := (regularStarts N L).powersetCard r)
    (fun I ↦ runRelativeNullity L I = 0)
  rw [card_powersetCard] at h
  change (directAt N L r).card +
    (((regularStarts N L).powersetCard r).filter (fun I ↦ runRelativeNullity L I ≠ 0)).card = _ at h
  omega

theorem failed_layer_eq (N L : ℕ) (e : Finset ℕ) (r : ℕ) (hr : 2 ≤ r) :
    (failedExtensions (fun x ↦ squareClassSpace x L) (regularStarts N L) e).filter
      (fun A ↦ A.card + 2 = r) = (((regularStarts N L) \ e).powersetCard (r - 2)).filter
        (fun A ↦ ¬ RetainedDependence.Compressed (fun x ↦ squareClassSpace x L) e (e ∪ A)) := by
  classical
  ext A
  simp only [failedExtensions, mem_filter, mem_powerset, mem_powersetCard]
  constructor
  · rintro ⟨⟨hsub, hnot⟩, hcard⟩
    exact ⟨⟨hsub, by omega⟩, hnot⟩
  · rintro ⟨⟨hsub, hcard⟩, hnot⟩
    exact ⟨⟨hsub, hnot⟩, by omega⟩

theorem failed_layer_empty (N L : ℕ) (e : Finset ℕ) (r : ℕ) (hr : r < 2) :
    (failedExtensions (fun x ↦ squareClassSpace x L) (regularStarts N L) e).filter
      (fun A ↦ A.card + 2 = r) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro A hA
  have hcard := (mem_filter.mp hA).2
  omega

theorem failed_layer_count {N L : ℕ} (hN : 2 ≤ N) (H : ℝ) (e : Finset ℕ)
    (he : e ∈ goodEdges H N L) (r : ℕ) (hr : 2 ≤ r) :
    ((failedExtensions (fun x ↦ squareClassSpace x L) (regularStarts N L) e).filter
      (fun A ↦ A.card + 2 = r)).card =
        ((regularStarts N L).card - 2).choose (r - 2) - (gamma N L e (r - 2)).card := by
  classical
  rw [failed_layer_eq N L e r hr]
  have h := card_filter_add_card_filter_not
    (s := ((regularStarts N L) \ e).powersetCard (r - 2))
    (fun A ↦ RetainedDependence.Compressed (fun x ↦ squareClassSpace x L) e (e ∪ A))
  rw [card_powersetCard, card_sdiff_of_subset (good_pair_regular hN e he), good_pair_card H N L e he] at h
  change (gamma N L e (r - 2)).card + _ = _ at h
  omega

theorem failed_size_bound {N L : ℕ} (hN : 2 ≤ N) (H : ℝ) (e : Finset ℕ)
    (he : e ∈ goodEdges H N L) (A : Finset ℕ)
    (hA : A ∈ failedExtensions (fun x ↦ squareClassSpace x L) (regularStarts N L) e) :
    A.card + 2 ≤ (regularStarts N L).card := by
  classical
  have hsub := mem_powerset.mp (mem_filter.mp hA).1
  have hcard := card_le_card hsub
  have heG := good_pair_regular hN e he
  have htwo := card_le_card heG
  rw [card_sdiff_of_subset heG, good_pair_card H N L e he] at hcard
  rw [good_pair_card H N L e he] at htwo
  omega

theorem directAt_source (N L r : ℕ) (I : Finset ℕ) :
    I ∈ directAt N L r ↔ I ⊆ regularStarts N L ∧ I.card = r ∧
      Function.Injective (relationAddition (fun i : I ↦ squareClassSpace i.val L)) := by
  simp only [directAt, mem_filter, mem_powersetCard]
  rw [CompressedBlocks.direct_family_iff_zero_nullity (fun x ↦ squareClassSpace x L) I]
  simp only [runRelativeNullity, and_assoc]

theorem gamma_source (N L : ℕ) (e A : Finset ℕ) (h : ℕ) :
    A ∈ gamma N L e h ↔ A ⊆ regularStarts N L \ e ∧ A.card = h ∧
      CompressedBlocks.Direct (fun x ↦ squareClassSpace x L) e (e ∪ A) := by
  simp only [gamma, mem_filter, mem_powersetCard]
  rw [CompressedBlocks.direct_iff_compressed _ e (e ∪ A) subset_union_left]
  exact and_assoc

theorem directAt_card_le (N L r : ℕ) : (directAt N L r).card ≤ (regularStarts N L).card.choose r := by
  have h := card_le_card (filter_subset (fun I ↦ runRelativeNullity L I = 0) ((regularStarts N L).powersetCard r))
  rw [card_powersetCard] at h
  exact h

theorem gamma_card_le {N L : ℕ} (hN : 2 ≤ N) (H : ℝ) (e : Finset ℕ)
    (he : e ∈ goodEdges H N L) (h : ℕ) :
    (gamma N L e h).card ≤ ((regularStarts N L).card - 2).choose h := by
  have hc := card_le_card (filter_subset
    (fun A ↦ RetainedDependence.Compressed (fun x ↦ squareClassSpace x L) e (e ∪ A))
    (((regularStarts N L) \ e).powersetCard h))
  rw [card_powersetCard, card_sdiff_of_subset (good_pair_regular hN e he), good_pair_card H N L e he] at hc
  exact hc

theorem firstCoefficient_real_formula (N L r : ℕ) :
    firstCoefficient N L r = ((2 ^ L : ℝ)⁻¹) ^ r *
      (((regularStarts N L).card.choose r : ℝ) - ((directAt N L r).card : ℝ)) := by
  rw [firstCoefficient, Nat.cast_sub (directAt_card_le N L r)]

theorem edgeCoefficient_real_formula {N L : ℕ} (hN : 2 ≤ N) (H : ℝ) (e : Finset ℕ)
    (he : e ∈ goodEdges H N L) (r : ℕ) (hr : 2 ≤ r) :
    edgeCoefficient N L e r = infiniteJointMoment L e * ((2 ^ L : ℝ)⁻¹) ^ (r - 2) *
      ((((regularStarts N L).card - 2).choose (r - 2) : ℝ) - ((gamma N L e (r - 2)).card : ℝ)) := by
  rw [edgeCoefficient, ite_eq_right (show ¬ r < 2 by omega), Nat.cast_sub (gamma_card_le hN H e he (r - 2))]

theorem firstCoefficient_nonneg (N L r : ℕ) : 0 ≤ firstCoefficient N L r := by
  unfold firstCoefficient
  positivity

theorem edgeCoefficient_nonneg (N L : ℕ) (e : Finset ℕ) (r : ℕ) : 0 ≤ edgeCoefficient N L e r := by
  unfold edgeCoefficient
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (mul_nonneg (infiniteJointMoment_nonneg L e) (by positivity)) (Nat.cast_nonneg _)

theorem secondCoefficient_nonneg (H : ℝ) (N L r : ℕ) : 0 ≤ secondCoefficient H N L r :=
  sum_nonneg (fun e _he ↦ edgeCoefficient_nonneg N L e r)

theorem firstCoefficient_zero_small (N L r : ℕ) (hr : r ≤ 1) : firstCoefficient N L r = 0 := by
  have hempty : ((regularStarts N L).powersetCard r).filter (fun I ↦ runRelativeNullity L I ≠ 0) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro I hI
    have hcard := (mem_powersetCard.mp (mem_filter.mp hI).1).2
    exact (mem_filter.mp hI).2
      (PaperP1.RetainedNullity.nullity_card_le_one (fun x ↦ squareClassSpace x L) I (by omega))
  rw [firstCoefficient, ← first_layer_count, hempty, card_empty, Nat.cast_zero, mul_zero]

theorem secondCoefficient_zero_small (H : ℝ) (N L r : ℕ) (hr : r < 2) : secondCoefficient H N L r = 0 := by
  unfold secondCoefficient
  apply sum_eq_zero
  intro e _he
  rw [edgeCoefficient, ite_eq_left hr]

theorem firstCoefficient_zero_large (N L r : ℕ) (hr : (regularStarts N L).card < r) :
    firstCoefficient N L r = 0 := by
  simp only [firstCoefficient, Nat.choose_eq_zero_of_lt hr, Nat.zero_sub, Nat.cast_zero, mul_zero]

theorem edgeCoefficient_zero_large {N L : ℕ} (hN : 2 ≤ N) (H : ℝ) (e : Finset ℕ)
    (he : e ∈ goodEdges H N L) (r : ℕ) (hr : (regularStarts N L).card < r) : edgeCoefficient N L e r = 0 := by
  by_cases hsmall : r < 2
  · rw [edgeCoefficient, ite_eq_left hsmall]
  · have hG := card_le_card (good_pair_regular hN e he)
    rw [good_pair_card H N L e he] at hG
    have hlt : (regularStarts N L).card - 2 < r - 2 := by omega
    simp only [edgeCoefficient, ite_eq_right hsmall, Nat.choose_eq_zero_of_lt hlt,
      Nat.zero_sub, Nat.cast_zero, mul_zero]

theorem secondCoefficient_zero_large {N L : ℕ} (hN : 2 ≤ N) (H : ℝ) (r : ℕ)
    (hr : (regularStarts N L).card < r) : secondCoefficient H N L r = 0 := by
  unfold secondCoefficient
  exact sum_eq_zero (fun e he ↦ edgeCoefficient_zero_large hN H e he r hr)

end PaperP1.RetainedCardinalityDeficits
