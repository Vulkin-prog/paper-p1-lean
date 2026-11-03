module

public import PaperP1.Arithmetic.TwoTargetClassSourceCover
public import PaperP1.Arithmetic.TwoTargetWindowSections
public import PaperP1.Arithmetic.TwoBlockComponentPatterns

/-! # The literal two-target products and disjoint integer offsets of physical label classes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetClassOffsets

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetWindowSections PaperP1.PositiveLineOffsetRoots PaperP1.SplitRadicalPointHeight
  PaperP1.TwoTargetClassSourceCover PaperP1.TwoTargetPrimeClassSupports

local instance classOffsetsPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance propDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def targetIndices {s L : ℕ} (D : Finset (TwoTargetWindowSections.Coordinate s L)) (j : Fin 2) :
    Finset (Fin (L + 1)) := univ.filter fun i ↦ ((Sum.inr j, i) : TwoTargetWindowSections.Coordinate s L) ∈ D

def targetVertices {s L : ℕ} (D : Finset (TwoTargetWindowSections.Coordinate s L)) (j : Fin 2) :
    Finset (TwoTargetWindowSections.Coordinate s L) :=
  (targetIndices D j).image fun i ↦ (Sum.inr j, i)

def targetOffsets {s L : ℕ} (D : Finset (TwoTargetWindowSections.Coordinate s L)) (j : Fin 2) : Finset ℤ :=
  integerOffsets (targetIndices D j)

theorem mem_target_indices {s L : ℕ} (D : Finset (TwoTargetWindowSections.Coordinate s L)) (j : Fin 2)
    (i : Fin (L + 1)) : i ∈ targetIndices D j ↔ ((Sum.inr j, i) : TwoTargetWindowSections.Coordinate s L) ∈ D := by
  simp only [targetIndices, mem_filter, mem_univ, true_and]

theorem target_vertices_eq {s L : ℕ} (D : Finset (TwoTargetWindowSections.Coordinate s L)) (j : Fin 2) :
    targetVertices D j = D ∩ univ.image (fun i : Fin (L + 1) ↦ ((Sum.inr j, i) : TwoTargetWindowSections.Coordinate s L)) := by
  ext v
  constructor
  · rintro hv
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hv
    exact mem_inter.mpr ⟨(mem_target_indices _ _ _).mp hi, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩
  · intro hv
    obtain ⟨hvD, hvT⟩ := mem_inter.mp hv
    obtain ⟨i, _hi, rfl⟩ := mem_image.mp hvT
    exact mem_image.mpr ⟨i, (mem_target_indices _ _ _).mpr hvD, rfl⟩

theorem target_vertices_disjoint {s L : ℕ} (D : Finset (TwoTargetWindowSections.Coordinate s L)) :
    Disjoint (targetVertices D 0) (targetVertices D 1) := by
  apply disjoint_left.mpr
  intro v hv0 hv1
  obtain ⟨i, _hi, hi⟩ := mem_image.mp hv0
  obtain ⟨j, _hj, hj⟩ := mem_image.mp hv1
  have h := congrArg Prod.fst (hi.trans hj.symm)
  exact (by decide : (0 : Fin 2) ≠ 1) (Sum.inr.inj h)

theorem target_vertices_union {s L : ℕ} (D : Finset (TwoTargetWindowSections.Coordinate s L)) :
    targetVertices D 0 ∪ targetVertices D 1 = D.filter (fun v ↦ ¬ IsSource v) := by
  ext v
  rw [target_vertices_eq, target_vertices_eq]
  rcases v with ⟨i | j, k⟩
  · simp [IsSource]
  · fin_cases j <;> simp [IsSource]

theorem target_indices_card {s L : ℕ} (D : Finset (TwoTargetWindowSections.Coordinate s L)) (j : Fin 2) :
    (targetIndices D j).card = (D ∩ univ.image (fun i : Fin (L + 1) ↦
      ((Sum.inr j, i) : TwoTargetWindowSections.Coordinate s L))).card := by
  rw [← target_vertices_eq, targetVertices]
  apply (card_image_of_injective _ ?_).symm
  intro i k h
  exact (Prod.mk.inj h).2

theorem target_offsets_card {s L : ℕ} (D : Finset (TwoTargetWindowSections.Coordinate s L)) (j : Fin 2) :
    (targetOffsets D j).card = (targetIndices D j).card := card_image_of_injective _ (integerOffset_injective L)

theorem offsets_nonempty_iff {s L : ℕ} (D : Finset (TwoTargetWindowSections.Coordinate s L)) (j : Fin 2) :
    (targetOffsets D j).Nonempty ↔ (D ∩ univ.image (fun i : Fin (L + 1) ↦
      ((Sum.inr j, i) : TwoTargetWindowSections.Coordinate s L))).Nonempty := by
  rw [← card_pos, target_offsets_card, target_indices_card, card_pos]

theorem total_card_le {s L : ℕ} (D : Finset (TwoTargetWindowSections.Coordinate s L)) :
    (targetOffsets D 0).card + (targetOffsets D 1).card ≤ D.card := by
  rw [target_offsets_card, target_offsets_card, target_indices_card, target_indices_card,
    ← target_vertices_eq, ← target_vertices_eq, ← card_union_of_disjoint (target_vertices_disjoint D),
    target_vertices_union]
  exact card_filter_le _ _

theorem offset_bound {s L : ℕ} (D : Finset (TwoTargetWindowSections.Coordinate s L)) (j : Fin 2)
    (z : ℤ) (hz : z ∈ targetOffsets D j) : z.natAbs ≤ L + 1 := by
  obtain ⟨i, _hi, rfl⟩ := mem_image.mp hz
  exact TwoBlockComponentPatterns.integerOffset_bound i

theorem offsets_disjoint {s L : ℕ} {D E : Finset (TwoTargetWindowSections.Coordinate s L)}
    (hDE : Disjoint D E) (j : Fin 2) : Disjoint (targetOffsets D j) (targetOffsets E j) := by
  rw [targetOffsets, targetOffsets, integerOffsets, integerOffsets, disjoint_image (integerOffset_injective L)]
  apply disjoint_left.mpr
  intro i hiD hiE
  exact disjoint_left.mp hDE ((mem_target_indices _ _ _).mp hiD) ((mem_target_indices _ _ _).mp hiE)

theorem class_offsets_disjoint {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (M : Submodule F₂ (code X L)) {α β : Module.Dual F₂ M} (hαβ : α ≠ β) (j : Fin 2) :
    Disjoint (targetOffsets (LabelClassPartition.part (label X M) α) j)
      (targetOffsets (LabelClassPartition.part (label X M) β) j) := by
  apply offsets_disjoint
  apply disjoint_left.mpr
  intro v hvα hvβ
  exact hαβ (((LabelClassPartition.mem_part _ _ _).mp hvα).symm.trans
    ((LabelClassPartition.mem_part _ _ _).mp hvβ))

theorem target_product_eq {s y z L : ℕ} (x : Fin s → ℕ) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (M : Submodule F₂ (code (starts x y z) L)) (α : Module.Dual F₂ M) :
    let D := LabelClassPartition.part (label (starts x y z) M) α
    (targetProduct (starts x y z) M α : ℤ) =
      integerProduct (targetOffsets D 0) (y : ℤ) * integerProduct (targetOffsets D 1) (z : ℤ) := by
  intro D
  change ((∏ v ∈ D.filter (fun v ↦ ¬ IsSource v), WindowPrimeIncidence.value (starts x y z) L v : ℕ) : ℤ) = _
  rw [← target_vertices_union, prod_union (target_vertices_disjoint D), Nat.cast_mul]
  have hproduct (j : Fin 2) :
      ((∏ v ∈ targetVertices D j, WindowPrimeIncidence.value (starts x y z) L v : ℕ) : ℤ) =
        integerProduct (targetOffsets D j) (if j = 0 then (y : ℤ) else z) := by
    rw [targetVertices, prod_image]
    · change ((∏ i ∈ targetIndices D j, startCompleteVertexLabel (if j = 0 then y else z) L i : ℕ) : ℤ) = _
      have hbase := TwoBlockComponentPatterns.start_product (x := if j = 0 then y else z)
        (by split_ifs <;> assumption) (targetIndices D j)
      by_cases hj : j = 0 <;> simpa only [targetOffsets, hj, ite_true, ite_false] using hbase
    · intro i _ k _ h
      exact (Prod.mk.inj h).2
  rw [hproduct 0, hproduct 1]
  simp only [ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]

theorem square_roots {s y z L d : ℕ} (x : Fin s → ℕ) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (M : Submodule F₂ (code (starts x y z) L)) (α : Module.Dual F₂ M)
    (hsquare : IsSquare ((d : ℤ) * targetProduct (starts x y z) M α)) :
    let D := LabelClassPartition.part (label (starts x y z) M) α
    ∃ w : ℤ, w ^ 2 = (d : ℤ) * integerProduct (targetOffsets D 0) (y : ℤ) *
      integerProduct (targetOffsets D 1) (z : ℤ) := by
  intro D
  rw [target_product_eq x hy hz M α] at hsquare
  obtain ⟨w, hw⟩ := hsquare
  exact ⟨w, by simpa only [pow_two, mul_assoc] using hw.symm⟩

end PaperP1.TwoTargetClassOffsets
