module

public import PaperP1.Combinatorics.OddLabelCircuitSupport
public import PaperP1.Arithmetic.WindowPrimeIncidence

/-! # Every large odd prime of an actual whole label class has a short support meeting a fixed source -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetPrimeClassSupports

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.WindowPrimeIncidence PaperP1.PhysicalLabelSupportCount

local instance twoTargetPrimeClassTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance dualDecidableEq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (M : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ M) := Classical.decEq _

abbrev label {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (v : (Fin s ⊕ Fin 2) × Fin (L + 1)) : Module.Dual F₂ M :=
  (CoordinateForms.coordinateFamily (code X L) v).comp M.subtype

abbrev allLabels {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L)) :=
  RecoveryLabelSupports.labels (CoordinateForms.coordinateFamily (code X L)) M

def classProduct {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (α : Module.Dual F₂ M) : ℕ :=
  ∏ v ∈ LabelClassPartition.part (label X M) α, value X L v

def throughPool {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (d : ℕ) (v : (Fin s ⊕ Fin 2) × Fin (L + 1)) : Finset (Finset ((Fin s ⊕ Fin 2) × Fin (L + 1))) :=
  (supportPool (label X M) (allLabels X M) d (label X M v)).image (insert v)

def classPool {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (d : ℕ) (α : Module.Dual F₂ M) : Finset (Finset ((Fin s ⊕ Fin 2) × Fin (L + 1))) :=
  (LabelClassPartition.part (label X M) α).biUnion (throughPool X M d)

theorem value_pos {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (hX : ∀ i, 2 ≤ X i)
    (v : (Fin s ⊕ Fin 2) × Fin (L + 1)) : 0 < value X L v := by
  have hx := hX v.1
  rw [value, startCompleteVertexLabel_eq_offset (by omega : 0 < X v.1)]
  omega

theorem odd_class_row {s L p : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (hX : ∀ i, 2 ≤ X i) (α : Module.Dual F₂ M)
    (hp : p ∈ DefectivePredicate.oddPrimeSupport (classProduct X M α)) :
    (∑ _v ∈ (occurrences X L p).filter (fun v ↦ label X M v = α), (1 : F₂)) = 1 := by
  have hne := LargeOddKernel.mem_oddPrimeSupport_iff_parityVec_ne_zero.mp hp
  have hparity : parityVec (classProduct X M α) p = 1 := by
    rcases binary_eq_zero_or_one (parityVec (classProduct X M α) p) with hz | ho
    · exact False.elim (hne hz)
    · exact ho
  rw [classProduct, parityVec_prod _ _ (fun v _ ↦ (value_pos X hX v).ne'), Finsupp.finsetSum_apply] at hparity
  have hset : (occurrences X L p).filter (fun v ↦ label X M v = α) =
      (LabelClassPartition.part (label X M) α).filter (fun v ↦ parityVec (value X L v) p = 1) := by
    ext v
    simp only [mem_filter, mem_occurrences, LabelClassPartition.mem_part]
    exact and_comm
  rw [hset, sum_filter]
  calc
    _ = ∑ v ∈ LabelClassPartition.part (label X M) α, parityVec (value X L v) p := by
      apply sum_congr rfl
      intro v _hv
      rcases binary_eq_zero_or_one (parityVec (value X L v) p) with hz | ho
      · simp only [hz, zero_ne_one, ite_false]
      · simp only [ho, ite_true]
    _ = _ := hparity

theorem source_support {s L H p : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (hX : ∀ i, 2 ≤ X i) (hH : L + 1 ≤ H) (hpH : H < p)
    (α : Module.Dual F₂ M) (hα : α ≠ 0)
    (hp : p ∈ DefectivePredicate.oddPrimeSupport (classProduct X M α)) :
    ∃ F ∈ classPool X M (s + 1) α, F ⊆ occurrences X L p ∧
      ∃ w ∈ F, ∃ i : Fin s, w.1 = Sum.inl i ∧ p ∣ startCompleteVertexLabel (X (Sum.inl i)) L w.2 := by
  have hXone : ∀ i, 1 ≤ X i := fun i ↦ (by have h := hX i; omega)
  have hpL := hH.trans_lt hpH
  have hcard := occurrences_card X L p hXone hpL
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  have hlabels : ∀ v ∈ occurrences X L p, label X M v ≠ 0 → label X M v ∈ allLabels X M := by
    intro v _hv hne
    exact (RecoveryLabelSupports.mem_labels _ M _).mpr ⟨hne, v, rfl⟩
  obtain ⟨v, hv, hva, D, _hD, hpool, _hzero, hsub, w, hw, i, hwi⟩ :=
    OddLabelCircuitSupport.source_support (label X M) (allLabels X M) (s + 1) (occurrences X L p) α
      Prod.fst (block_injective X L p hXone hpL) hα (by omega) (restricted_row_sum X L p M) hlabels
      (odd_class_row X M hX α hp)
  have hclass : v ∈ LabelClassPartition.part (label X M) α := (LabelClassPartition.mem_part _ _ _).mpr hva
  have hF : insert v D ∈ classPool X M (s + 1) α := by
    apply mem_biUnion.mpr
    refine ⟨v, hclass, mem_image.mpr ⟨D, ?_, rfl⟩⟩
    simpa only [hva] using hpool
  have hdiv := dvd_of_mem (hsub hw)
  exact ⟨insert v D, hF, hsub, w, hw, i, hwi, by simpa only [value, hwi] using hdiv⟩

end PaperP1.TwoTargetPrimeClassSupports
