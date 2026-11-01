module

public import PaperP1.Coding.RegularizedSupportPools
public import PaperP1.Coding.ProjectionLabelBudget

/-! # A large actual target projection retains many labels and finite support pools -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RegularizedProjection

open Finset PaperP1.Affine PaperP1.DisjointRecoveryTheorem
  PaperP1.PhysicalLabelSupportCount PaperP1.RecoveryLabelSupports

variable {U V I : Type*} [AddCommGroup U] [Module 𝔽₂ U] [FiniteDimensional 𝔽₂ U]
  [Fintype V] [DecidableEq V] [Fintype I]

local instance regularizedProjectionDualDecEq (M : Submodule 𝔽₂ U) : DecidableEq (Module.Dual 𝔽₂ M) :=
  Classical.decEq _

omit [FiniteDimensional 𝔽₂ U] [DecidableEq V] in
theorem target_labels_subset (L : V → Module.Dual 𝔽₂ U) (f : U →ₗ[𝔽₂] (I → 𝔽₂))
    (target : I → V) (hcoord : ∀ u i, f u i = L (target i) u) (M : Submodule 𝔽₂ U) :
    ProjectionLabelBudget.labels (f.comp M.subtype) ⊆ labels L M := by
  intro a ha
  obtain ⟨hane, i, hi⟩ := (ProjectionLabelBudget.mem_labels _ a).mp ha
  apply (mem_labels L M a).mpr
  refine ⟨hane, target i, ?_⟩
  calc
    _ = ProjectionLabelBudget.form (f.comp M.subtype) i := by
      ext u
      exact (hcoord u.val i).symm
    _ = a := hi

theorem regularized_projection (L : V → Module.Dual 𝔽₂ U) (f : U →ₗ[𝔽₂] (I → 𝔽₂))
    (target : I → V) (hcoord : ∀ u i, f u i = L (target i) u)
    (d t : ℕ) (hd : 1 ≤ d) (ht : 2 ≤ t) :
    ∃ M : Submodule 𝔽₂ U, RecoveryConclusion L M d t (t - 1) ∧
      (Module.finrank 𝔽₂ (LinearMap.range f) : ℝ) -
        2 * (Fintype.card V : ℝ) * DisjointRecoveryParameters.parameter d t ≤
          (ProjectionLabelBudget.labels (f.comp M.subtype)).card ∧
      ProjectionLabelBudget.labels (f.comp M.subtype) ⊆ labels L M ∧
      ∀ α : Module.Dual 𝔽₂ M, α ≠ 0 →
        (supportPool (fun v ↦ (L v).comp M.subtype) (labels L M) d α).card ≤
          supportBound d t (t - 1) := by
  obtain ⟨M, hM, hpools⟩ := RegularizedSupportPools.regularized_pools L d t hd ht
  refine ⟨M, hM, ?_, target_labels_subset L f target hcoord M, hpools⟩
  have hproj := ProjectionLabelBudget.restricted_labels_lower_bound f M
  have hcost := hM.1
  linarith only [hproj, hcost]

end PaperP1.RegularizedProjection
