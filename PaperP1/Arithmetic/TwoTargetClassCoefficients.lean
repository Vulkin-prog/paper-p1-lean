module

public import PaperP1.Arithmetic.TwoTargetClassSourceCover
public import PaperP1.Arithmetic.SourceSupportedCoefficientPool
public import PaperP1.Arithmetic.FixedSourceCertificate

/-! # A single actual source-dependent coefficient pool contains every two-target label class equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetClassCoefficients

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.WindowPrimeIncidence PaperP1.TwoTargetPrimeClassSupports PaperP1.TwoTargetClassSourceCover
  PaperP1.PhysicalLabelSupportCount PaperP1.DisjointRecoveryTheorem PaperP1.SmallPrimeBudget

local instance twoTargetClassCoeffTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance dualDecidableEq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (M : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ M) := Classical.decEq _

def sourceBound (s t : ℕ) : ℕ :=
  (t - 1) + ((t - 1) * supportBound (s + 1) t (t - 1)) * ((s + 1) * (t - 1) + 1)

def sourceIndices {s L : ℕ} (C : Finset ((Fin s ⊕ Fin 2) × Fin (L + 1))) : Finset (Fin s × Fin (L + 1)) :=
  univ.filter fun v ↦ (Sum.inl v.1, v.2) ∈ C

theorem source_indices_image {s L : ℕ} (C : Finset ((Fin s ⊕ Fin 2) × Fin (L + 1)))
    (hC : ∀ v ∈ C, IsSource v) :
    (sourceIndices C).image (fun v ↦ ((Sum.inl v.1, v.2) : (Fin s ⊕ Fin 2) × Fin (L + 1))) = C := by
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hv
    exact (mem_filter.mp hw).2
  · intro hv
    obtain ⟨i, hi⟩ := hC v hv
    have heq : ((Sum.inl i, v.2) : (Fin s ⊕ Fin 2) × Fin (L + 1)) = v := Prod.ext hi.symm rfl
    exact mem_image.mpr ⟨(i, v.2), mem_filter.mpr ⟨mem_univ _, heq.symm ▸ hv⟩, heq⟩

theorem source_indices_card {s L : ℕ} (C : Finset ((Fin s ⊕ Fin 2) × Fin (L + 1)))
    (hC : ∀ v ∈ C, IsSource v) : (sourceIndices C).card = C.card := by
  have hinj : Function.Injective (fun v : Fin s × Fin (L + 1) ↦
      ((Sum.inl v.1, v.2) : (Fin s ⊕ Fin 2) × Fin (L + 1))) := by
    intro v w h
    exact Prod.ext (Sum.inl.inj (Prod.mk.inj h).1) (Prod.mk.inj h).2
  calc
    _ = ((sourceIndices C).image (fun v ↦ ((Sum.inl v.1, v.2) : (Fin s ⊕ Fin 2) × Fin (L + 1)))).card :=
      (card_image_of_injective _ hinj).symm
    _ = _ := congrArg Finset.card (source_indices_image C hC)

theorem cover_product_eq {s L d : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (hX : ∀ i, 2 ≤ X i) (α : Module.Dual F₂ M) :
    (sourceIndices (sourceCover X M d α)).prod
      (FixedSourceCertificate.sourceValues (fun i ↦ X (Sum.inl i)) (L + 1)) = coverProduct X M d α := by
  have h := congrArg (fun C ↦ C.prod (value X L))
    (source_indices_image (sourceCover X M d α) (fun _ hv ↦ source_cover_is_source X M α hv))
  rw [prod_image] at h
  · apply Eq.trans ?_ h
    apply prod_congr rfl
    intro v _hv
    have hx := hX (Sum.inl v.1)
    simp only [value, startCompleteVertexLabel_eq_offset (by omega : 0 < X (Sum.inl v.1)),
      FixedSourceCertificate.sourceValues]
  · intro v _hv w _hw h
    exact Prod.ext (Sum.inl.inj (Prod.mk.inj h).1) (Prod.mk.inj h).2

theorem kernel_in_pool {s L H t : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (hX : ∀ i, 2 ≤ X i) (hH : L + 1 ≤ H) (ht : 2 ≤ t)
    (hM : RecoveryConclusion (CoordinateForms.coordinateFamily (code X L)) M (s + 1) t (t - 1))
    (α : Module.Dual F₂ M) (hα : α ≠ 0) :
    squarefreeKernel (targetProduct X M α) ∈ SourceSupportedCoefficientPool.pool
      (FixedSourceCertificate.sourceValues (fun i ↦ X (Sum.inl i)) (L + 1)) H (sourceBound s t) := by
  let A := sourceIndices (sourceCover X M (s + 1) α)
  have hA : A.card ≤ sourceBound s t := by
    rw [source_indices_card _ (fun _ hv ↦ source_cover_is_source X M α hv)]
    exact recovery_source_cover_card X M ht hM α hα
  have hproduct := cover_product_eq (d := s + 1) X M hX α
  have hm : 0 < A.prod (FixedSourceCertificate.sourceValues (fun i ↦ X (Sum.inl i)) (L + 1)) := by
    rw [hproduct]
    exact prod_pos fun v _ ↦ TwoTargetPrimeClassSupports.value_pos X hX v
  apply SourceSupportedCoefficientPool.kernel_mem _ H (sourceBound s t) _ A hA hm
  rw [hproduct]
  exact target_kernel_dvd_cover X M hX hH α hα

theorem class_equation {s L H t : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (hX : ∀ i, 2 ≤ X i) (hH : L + 1 ≤ H) (ht : 2 ≤ t)
    (hM : RecoveryConclusion (CoordinateForms.coordinateFamily (code X L)) M (s + 1) t (t - 1))
    (α : Module.Dual F₂ M) (hα : α ≠ 0) :
    ∃ D ∈ SourceSupportedCoefficientPool.pool
      (FixedSourceCertificate.sourceValues (fun i ↦ X (Sum.inl i)) (L + 1)) H (sourceBound s t),
      IsSquare ((D : ℤ) * targetProduct X M α) := by
  refine ⟨squarefreeKernel (targetProduct X M α), kernel_in_pool X M hX hH ht hM α hα, ?_⟩
  have hn : 0 < targetProduct X M α := prod_pos fun v _ ↦ TwoTargetPrimeClassSupports.value_pos X hX v
  obtain ⟨r, hr⟩ := RelativeSquarefreeParts.kernel_mul_isSquare hn.ne'
  exact ⟨(r : ℤ), by exact_mod_cast hr⟩

theorem kernel_height {s L N K : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (hX : ∀ i, 2 ≤ X i) (hN : 1 ≤ N) (α : Module.Dual F₂ M)
    (hclass : (LabelClassPartition.part (label X M) α).card ≤ K)
    (hheight : ∀ v ∈ LabelClassPartition.part (label X M) α, value X L v ≤ N ^ 2) :
    squarefreeKernel (targetProduct X M α) ≤ N ^ (2 * K) := by
  classical
  have hn : 0 < targetProduct X M α := prod_pos fun v _ ↦ TwoTargetPrimeClassSupports.value_pos X hX v
  have hdiv : squarefreeKernel (targetProduct X M α) ∣ targetProduct X M α :=
    ⟨DefectivePredicate.canonicalSquarePart (targetProduct X M α) ^ 2,
      (squarefreeKernel_mul_squarePart hn.ne').symm⟩
  apply (Nat.le_of_dvd hn hdiv).trans
  have hcard : ((LabelClassPartition.part (label X M) α).filter fun v ↦ ¬ IsSource v).card ≤ K :=
    (card_filter_le _ _).trans hclass
  calc
    _ ≤ ∏ _v ∈ (LabelClassPartition.part (label X M) α).filter (fun v ↦ ¬ IsSource v), N ^ 2 :=
      prod_le_prod fun v hv ↦ hheight v (mem_filter.mp hv).1
    _ = N ^ (2 * ((LabelClassPartition.part (label X M) α).filter fun v ↦ ¬ IsSource v).card) := by
      rw [prod_const, ← pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by omega : 0 < N) (Nat.mul_le_mul_left 2 hcard)

end PaperP1.TwoTargetClassCoefficients
