module

public import PaperP1.Arithmetic.TwoTargetPrimeClassSupports
public import PaperP1.Combinatorics.PhysicalSupportPoolBudget
public import PaperP1.Arithmetic.LargeOddKernel

/-! # A bounded actual source-coordinate cover contains every large odd prime of a target class product -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetClassSourceCover

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.WindowPrimeIncidence PaperP1.PhysicalLabelSupportCount
  PaperP1.TwoTargetPrimeClassSupports PaperP1.DisjointRecoveryTheorem PaperP1.LargeOddKernel

local instance twoTargetSourceCoverTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance classicalDecidable (P : Prop) : Decidable P := Classical.propDecidable P
local instance dualDecidableEq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (M : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ M) := Classical.decEq _

def IsSource {s L : ℕ} (v : (Fin s ⊕ Fin 2) × Fin (L + 1)) : Prop :=
  ∃ i : Fin s, v.1 = Sum.inl i

def sourceVertices {s L : ℕ} (C : Finset ((Fin s ⊕ Fin 2) × Fin (L + 1))) := C.filter IsSource

def sourceCover {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (d : ℕ) (α : Module.Dual F₂ M) :=
  sourceVertices (LabelClassPartition.part (label X M) α) ∪
    (classPool X M d α).biUnion sourceVertices

def sourceProduct {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (α : Module.Dual F₂ M) : ℕ :=
  ∏ v ∈ sourceVertices (LabelClassPartition.part (label X M) α), value X L v

def targetProduct {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (α : Module.Dual F₂ M) : ℕ :=
  ∏ v ∈ (LabelClassPartition.part (label X M) α).filter (fun v ↦ ¬ IsSource v), value X L v

def coverProduct {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (d : ℕ) (α : Module.Dual F₂ M) : ℕ := ∏ v ∈ sourceCover X M d α, value X L v

theorem source_cover_is_source {s L d : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (α : Module.Dual F₂ M) {v : (Fin s ⊕ Fin 2) × Fin (L + 1)} (hv : v ∈ sourceCover X M d α) : IsSource v := by
  rcases mem_union.mp hv with hv | hv
  · exact (mem_filter.mp hv).2
  · obtain ⟨F, _hF, hvF⟩ := mem_biUnion.mp hv
    exact (mem_filter.mp hvF).2

theorem class_pool_card {s L d K B : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (α : Module.Dual F₂ M) (hclass : (LabelClassPartition.part (label X M) α).card ≤ K)
    (hpool : (supportPool (label X M) (allLabels X M) d α).card ≤ B) :
    (classPool X M d α).card ≤ K * B := by
  have hthrough : ∀ v ∈ LabelClassPartition.part (label X M) α, (throughPool X M d v).card ≤ B := by
    intro v hv
    have heq := (LabelClassPartition.mem_part _ _ _).mp hv
    exact card_image_le.trans (by simpa only [heq] using hpool)
  calc
    _ ≤ ∑ v ∈ LabelClassPartition.part (label X M) α, (throughPool X M d v).card := card_biUnion_le
    _ ≤ ∑ _v ∈ LabelClassPartition.part (label X M) α, B := sum_le_sum hthrough
    _ = (LabelClassPartition.part (label X M) α).card * B := by simp
    _ ≤ _ := Nat.mul_le_mul_right B hclass

theorem class_pool_member_card {s L d K : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (hK : ∀ a ∈ allLabels X M, (fibre (label X M) a).card ≤ K)
    (α : Module.Dual F₂ M) {F : Finset ((Fin s ⊕ Fin 2) × Fin (L + 1))}
    (hF : F ∈ classPool X M d α) : F.card ≤ d * K + 1 := by
  obtain ⟨v, _hv, hFv⟩ := mem_biUnion.mp hF
  obtain ⟨D, hD, rfl⟩ := mem_image.mp hFv
  exact PhysicalSupportPoolBudget.inserted_member_card (label X M) (allLabels X M) d K hK _ v hD

theorem source_cover_card {s L d K B : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (hK : ∀ a ∈ allLabels X M, (fibre (label X M) a).card ≤ K)
    (α : Module.Dual F₂ M) (hclass : (LabelClassPartition.part (label X M) α).card ≤ K)
    (hpool : (supportPool (label X M) (allLabels X M) d α).card ≤ B) :
    (sourceCover X M d α).card ≤ K + (K * B) * (d * K + 1) := by
  have hc : (sourceVertices (LabelClassPartition.part (label X M) α)).card ≤ K :=
    (card_filter_le _ _).trans hclass
  have hp := class_pool_card X M α hclass hpool
  have hmember : ∀ F ∈ classPool X M d α, (sourceVertices F).card ≤ d * K + 1 :=
    fun F hF ↦ (card_filter_le _ _).trans (class_pool_member_card X M hK α hF)
  have hsum := (card_biUnion_le_card_mul (classPool X M d α) sourceVertices (d * K + 1) hmember).trans
    (Nat.mul_le_mul_right _ hp)
  exact (card_union_le _ _).trans (Nat.add_le_add hc hsum)

theorem recovery_source_cover_card {s L d t : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (ht : 2 ≤ t) (hM : RecoveryConclusion (CoordinateForms.coordinateFamily (code X L)) M d t (t - 1))
    (α : Module.Dual F₂ M) (hα : α ≠ 0) :
    (sourceCover X M d α).card ≤ (t - 1) + ((t - 1) * supportBound d t (t - 1)) * (d * (t - 1) + 1) := by
  have hno := RecoveryLabelSupports.noDisjointSums_of_recovery_exclusion
    (CoordinateForms.coordinateFamily (code X L)) M d t (by omega) hM.2.1
  have hK : ∀ a ∈ allLabels X M, (fibre (label X M) a).card ≤ t - 1 := by
    intro a ha
    exact hM.2.2.1 a ((RecoveryLabelSupports.mem_labels _ M a).mp ha).1
  have hp := supportPool_card (label X M) (allLabels X M) d t (t - 1) hno hK α hα
  exact source_cover_card X M hK α (hM.2.2.1 α hα) hp

theorem class_product_eq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (α : Module.Dual F₂ M) : classProduct X M α = sourceProduct X M α * targetProduct X M α :=
  (prod_filter_mul_prod_filter_not (LabelClassPartition.part (label X M) α) IsSource (value X L)).symm

theorem target_kernel_dvd_cover {s L H : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (hX : ∀ i, 2 ≤ X i) (hH : L + 1 ≤ H) (α : Module.Dual F₂ M) (hα : α ≠ 0) :
    largeOddKernel H (targetProduct X M α) ∣ coverProduct X M (s + 1) α := by
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (prime_of_mem_oddPrimeSupport (mem_filter.mp hp).1).prime
  · intro p hp
    obtain ⟨hpodd, hpH⟩ := mem_filter.mp hp
    have hpprime := prime_of_mem_oddPrimeSupport hpodd
    by_cases hpsource : p ∣ sourceProduct X M α
    · obtain ⟨v, hv, hpv⟩ := hpprime.prime.dvd_finsetProd_iff (value X L) |>.mp hpsource
      exact hpv.trans (dvd_prod_of_mem (value X L) (mem_union.mpr (Or.inl hv)))
    · have hsourcepos : 0 < sourceProduct X M α :=
        prod_pos fun v _ ↦ TwoTargetPrimeClassSupports.value_pos X hX v
      have htargetpos : 0 < targetProduct X M α :=
        prod_pos fun v _ ↦ TwoTargetPrimeClassSupports.value_pos X hX v
      have hsourcezero : parityVec (sourceProduct X M α) p = 0 := by
        simp only [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd hpsource, Nat.cast_zero]
      have hpclass : p ∈ DefectivePredicate.oddPrimeSupport (classProduct X M α) := by
        apply mem_oddPrimeSupport_iff_parityVec_ne_zero.mpr
        rw [class_product_eq, parityVec_mul hsourcepos.ne' htargetpos.ne', Finsupp.add_apply, hsourcezero, zero_add]
        exact mem_oddPrimeSupport_iff_parityVec_ne_zero.mp hpodd
      obtain ⟨F, hF, _hFR, w, hw, i, hwi, hdiv⟩ := TwoTargetPrimeClassSupports.source_support X M hX hH hpH α hα hpclass
      have hwsource : w ∈ sourceVertices F := mem_filter.mpr ⟨hw, i, hwi⟩
      have hwcover : w ∈ sourceCover X M (s + 1) α :=
        mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨F, hF, hwsource⟩))
      have hpw : p ∣ value X L w := by simpa only [value, hwi] using hdiv
      exact hpw.trans (dvd_prod_of_mem (value X L) hwcover)

end PaperP1.TwoTargetClassSourceCover
