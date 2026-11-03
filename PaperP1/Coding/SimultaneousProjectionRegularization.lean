module

public import PaperP1.Coding.RegularizedProjection

/-! # One regularized relation space retains the separate label count in every injective target -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SimultaneousProjectionRegularization

open Finset PaperP1.Affine PaperP1.DisjointRecoveryTheorem PaperP1.RecoveryLabelSupports
  PaperP1.PhysicalLabelSupportCount

variable {U V I T : Type*} [AddCommGroup U] [Module 𝔽₂ U] [FiniteDimensional 𝔽₂ U]
  [Fintype V] [DecidableEq V] [Fintype I]

local instance dualDecidableEq (M : Submodule 𝔽₂ U) : DecidableEq (Module.Dual 𝔽₂ M) :=
  Classical.decEq _

theorem common_regularization (L : V → Module.Dual 𝔽₂ U)
    (f : T → U →ₗ[𝔽₂] (I → 𝔽₂)) (target : T → I → V)
    (hcoord : ∀ t u i, f t u i = L (target t i) u) (hinj : ∀ t, Function.Injective (f t))
    (d t : ℕ) (hd : 1 ≤ d) (ht : 2 ≤ t) :
    ∃ M : Submodule 𝔽₂ U, RecoveryConclusion L M d t (t - 1) ∧
      (∀ j, (Module.finrank 𝔽₂ U : ℝ) -
        2 * (Fintype.card V : ℝ) * DisjointRecoveryParameters.parameter d t ≤
          (ProjectionLabelBudget.labels ((f j).comp M.subtype)).card) ∧
      (∀ j, ProjectionLabelBudget.labels ((f j).comp M.subtype) ⊆ labels L M) ∧
      ∀ α : Module.Dual 𝔽₂ M, α ≠ 0 →
        (supportPool (fun v ↦ (L v).comp M.subtype) (labels L M) d α).card ≤
          supportBound d t (t - 1) := by
  classical
  obtain ⟨M, hM, hpools⟩ := RegularizedSupportPools.regularized_pools L d t hd ht
  refine ⟨M, hM, ?_, fun j ↦ RegularizedProjection.target_labels_subset L (f j) (target j) (hcoord j) M,
    hpools⟩
  intro j
  have hproj := ProjectionLabelBudget.restricted_labels_lower_bound (f j) M
  rw [LinearMap.finrank_range_of_inj (hinj j)] at hproj
  have hcost := hM.1
  linarith only [hproj, hcost]

end PaperP1.SimultaneousProjectionRegularization
