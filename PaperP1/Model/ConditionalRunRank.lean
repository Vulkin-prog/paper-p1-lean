module

public import PaperP1.Arithmetic.ConditionalWindowRank
public import PaperP1.Affine.StartCharacterSpace
public import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Conditional square-class nullity equals the actual run-row nullity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConditionalRunRank

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
  PaperP1.WindowRelationCode PaperP1.ConditionalWindowRank

def oldRows (M : ℕ) (R : Finset ℕ) : Submodule F₂ (SampleSpace M →ₗ[F₂] F₂) :=
  (oldSpan R).map (parityPairing M)

theorem oldSpan_le_bounded {M : ℕ} {R : Finset ℕ} (hR : ∀ n ∈ R, n ≤ M) :
    oldSpan R ≤ boundedPrimeParity M := by
  apply Submodule.span_le.mpr
  rintro _ ⟨n, hn, rfl⟩
  exact parityVec_mem_boundedPrimeParity (hR n hn)

theorem pairing_mem_oldRows_iff {M : ℕ} {R : Finset ℕ} (hR : ∀ n ∈ R, n ≤ M)
    {v : ℕ →₀ F₂} (hv : v ∈ boundedPrimeParity M) :
    parityPairing M v ∈ oldRows M R ↔ v ∈ oldSpan R := by
  constructor
  · rintro ⟨w, hw, heq⟩
    have h := parityPairing_injOn_bounded M (oldSpan_le_bounded hR hw) hv heq
    exact h ▸ hw
  · intro hw
    exact Submodule.mem_map.mpr ⟨v, hw, rfl⟩

theorem start_sum_eq_window (L : ℕ) : startVertexSum L = windowEvennessMap (L + 1) := by
  apply LinearMap.ext
  intro w
  simp only [startVertexSum_apply, windowEvennessMap, Fintype.linearCombination_apply,
    smul_eq_mul, mul_one]

def rowBoundaryEquiv (L : ℕ) : (Fin L → F₂) ≃ₗ[F₂] LinearMap.ker (windowEvennessMap (L + 1)) :=
  (startBoundaryEquivEven L).trans (LinearEquiv.ofEq _ _ (congrArg LinearMap.ker (start_sum_eq_window L)))

theorem rowBoundaryEquiv_apply_coe (L : ℕ) (u : Fin L → F₂) :
    (rowBoundaryEquiv L u).val = startCompleteBoundary L u := by
  simp only [rowBoundaryEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    startBoundaryEquivEven_apply_coe]

theorem evenMap_boundary {x L : ℕ} (hx : 0 < x) (u : Fin L → F₂) :
    evenMap (x - 1) (L + 1) (rowBoundaryEquiv L u) =
      vertexParityMap x L (startCompleteBoundary L u) := by
  change windowParityMap (x - 1) (L + 1) (rowBoundaryEquiv L u).val = _
  rw [rowBoundaryEquiv_apply_coe, vertexParityMap_apply]
  simp only [windowParityMap, Fintype.linearCombination_apply, startCompleteVertexLabel_eq_offset hx]

theorem row_kernel_mem_iff {M x L : ℕ} {R : Finset ℕ}
    (hx : 0 < x) (hcut : x + L ≤ M) (hR : ∀ n ∈ R, n ≤ M) (u : Fin L → F₂) :
    u ∈ (oldRows M R).comap (relationMap (startSystem M x L)) ↔
      rowBoundaryEquiv L u ∈ relativeKernel R (x - 1) (L + 1) := by
  change relationMap (startSystem M x L) u ∈ oldRows M R ↔ _
  rw [relationMap_start_eq_parityPairing]
  change parityPairing M (vertexParityMap x L (startCompleteBoundary L u)) ∈ oldRows M R ↔ _
  rw [pairing_mem_oldRows_iff hR]
  · change _ ↔ evenMap (x - 1) (L + 1) (rowBoundaryEquiv L u) ∈ oldSpan R
    rw [evenMap_boundary hx]
  · have hv : vertexParityMap x L (startCompleteBoundary L u) ∈ squareClassSpace x L :=
      ⟨startBoundaryToEven L u, rfl⟩
    exact squareClassSpace_le_boundedPrimeParity hcut hv

def rowKernelEquiv {M x L : ℕ} {R : Finset ℕ}
    (hx : 0 < x) (hcut : x + L ≤ M) (hR : ∀ n ∈ R, n ≤ M) :
    (oldRows M R).comap (relationMap (startSystem M x L)) ≃ₗ[F₂]
      relativeKernel R (x - 1) (L + 1) :=
  (rowBoundaryEquiv L).ofSubmodules _ _ (by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (row_kernel_mem_iff hx hcut hR u).mp hu
    · intro hw
      let u := (rowBoundaryEquiv L).symm w
      have hu : u ∈ (oldRows M R).comap (relationMap (startSystem M x L)) := by
        apply (row_kernel_mem_iff hx hcut hR u).mpr
        simpa only [u, LinearEquiv.apply_symm_apply] using hw
      exact ⟨u, hu, (rowBoundaryEquiv L).apply_symm_apply w⟩)

theorem row_kernel_finrank {M x L : ℕ} {R : Finset ℕ}
    (hx : 0 < x) (hcut : x + L ≤ M) (hR : ∀ n ∈ R, n ≤ M) :
    Module.finrank F₂ ((oldRows M R).comap (relationMap (startSystem M x L))) =
      conditionalNullity R (x - 1) (L + 1) := (rowKernelEquiv hx hcut hR).finrank_eq

end PaperP1.ConditionalRunRank
