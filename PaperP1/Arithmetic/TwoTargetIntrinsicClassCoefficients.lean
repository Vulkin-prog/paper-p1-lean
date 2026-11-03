module

public import PaperP1.Arithmetic.TwoTargetClassCoefficients

/-! # The actual coefficient pool uses only intrinsic recovery exclusion, with no ambient codimension premise -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetIntrinsicClassCoefficients

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetPrimeClassSupports PaperP1.TwoTargetClassSourceCover PaperP1.TwoTargetClassCoefficients
  PaperP1.DisjointRecoverySubspace PaperP1.PhysicalLabelSupportCount

local instance intrinsicClassPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance dualDecidableEq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (M : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ M) := Classical.decEq _

theorem source_cover_card {s L t : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (ht : 2 ≤ t) (hno : NoDisjointRecovery (CoordinateForms.coordinateFamily (code X L)) M (s + 1) t)
    (α : Module.Dual F₂ M) (hα : α ≠ 0) :
    (sourceCover X M (s + 1) α).card ≤ sourceBound s t := by
  have hsum := RecoveryLabelSupports.noDisjointSums_of_recovery_exclusion
    (CoordinateForms.coordinateFamily (code X L)) M (s + 1) t (by omega) hno
  have hmult := coordinate_multiplicity_le (CoordinateForms.coordinateFamily (code X L)) M
    (s + 1) t (by omega) hno
  have hK : ∀ a ∈ allLabels X M, (fibre (label X M) a).card ≤ t - 1 := by
    intro a ha
    exact hmult a ((RecoveryLabelSupports.mem_labels _ M a).mp ha).1
  have hp := supportPool_card (label X M) (allLabels X M) (s + 1) t (t - 1) hsum hK α hα
  exact TwoTargetClassSourceCover.source_cover_card X M hK α (hmult α hα) hp

theorem kernel_in_pool {s L H t : ℕ} (X : Fin s ⊕ Fin 2 → ℕ) (M : Submodule F₂ (code X L))
    (hX : ∀ i, 2 ≤ X i) (hH : L + 1 ≤ H) (ht : 2 ≤ t)
    (hno : NoDisjointRecovery (CoordinateForms.coordinateFamily (code X L)) M (s + 1) t)
    (α : Module.Dual F₂ M) (hα : α ≠ 0) :
    SmallPrimeBudget.squarefreeKernel (targetProduct X M α) ∈ SourceSupportedCoefficientPool.pool
      (FixedSourceCertificate.sourceValues (fun i ↦ X (Sum.inl i)) (L + 1)) H (sourceBound s t) := by
  let A := sourceIndices (sourceCover X M (s + 1) α)
  have hA : A.card ≤ sourceBound s t := by
    rw [source_indices_card _ (fun _ hv ↦ source_cover_is_source X M α hv)]
    exact source_cover_card X M ht hno α hα
  have hproduct := cover_product_eq (d := s + 1) X M hX α
  have hm : 0 < A.prod (FixedSourceCertificate.sourceValues (fun i ↦ X (Sum.inl i)) (L + 1)) := by
    rw [hproduct]
    exact prod_pos fun v _ ↦ TwoTargetPrimeClassSupports.value_pos X hX v
  apply SourceSupportedCoefficientPool.kernel_mem _ H (sourceBound s t) _ A hA hm
  rw [hproduct]
  exact target_kernel_dvd_cover X M hX hH α hα

end PaperP1.TwoTargetIntrinsicClassCoefficients
