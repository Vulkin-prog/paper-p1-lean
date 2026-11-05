module

public import PaperP1.Asymptotics.DenseAnchoredKernelWitness
public import PaperP1.Arithmetic.PhysicalWindowReindex
public import PaperP1.Arithmetic.FixedArityPhysicalSubspaceRegularization
public import PaperP1.Combinatorics.PointedFiniteEnumeration

/-! # A dense physical relation at any actual anchor has a uniform kernel witness

A fresh regularization is constructed after exact index transport. The input
subspace has no recovery-exclusion hypothesis. Only the selected projection
must be injective and only its active nonalignment with other blocks is used.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DensePhysicalAnchorWitness

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.ActivePhysicalPrimeGroups PaperP1.Model

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance codeAddCommGroup {ι : Type*} [Fintype ι] (X : ι → ℕ) (L : ℕ) : AddCommGroup (code X L) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := ((ι × Fin (L + 1)) → F₂)) (code X L)
local instance physicalAddCommGroup {ι : Type*} [Fintype ι] (X : ι → ℕ) (L : ℕ)
    (M : Submodule F₂ (code X L)) : AddCommGroup M := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := code X L) M

theorem uniform_parameter (s : ℕ) (hs : 1 ≤ s) (η : ℝ) (hη : 0 < η) :
    ∃ t : ℕ, 2 ≤ t ∧ ∀ C τ : ℝ, 0 < τ →
      ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ (ι : Type*) [Fintype ι] [DecidableEq ι], Fintype.card ι = s + 1 →
      ∀ X : ι → ℕ, (∀ i, X i ∈ dyadicBlock N) →
      ∀ (M : Submodule F₂ (code X L)) (H : ℕ), L + 1 ≤ H → ∀ i : ι,
      OffsetNonalignmentFrom.NoExactFrom X L (fun v ↦ label X L M v ≠ 0) i →
      η * L ≤ (Module.finrank F₂ M : ℝ) →
      Function.Injective ((projection X L i).comp M.subtype) →
      X i ∈ SmallKernelWindowSets.twoWindows N L H
        (2 * τ * (PhysicalLabelSupportCount.supportBound s t (t - 1) : ℝ)) := by
  obtain ⟨t, ht, hreg⟩ := FixedArityPhysicalSubspaceRegularization.uniform_subspace s hs η hη
  refine ⟨t, ht, ?_⟩
  intro C τ hτ
  obtain ⟨NW, _hNW, hw⟩ := DenseAnchoredKernelWitness.uniform_witness
    s hs C τ (η / 2) hτ (by positivity) t ht
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨3 + NW + NG, by omega, ?_⟩
  intro N hN L hband ι _ _ hcard X hX M H hH i hno hdense hinj
  classical
  have hL : 1 ≤ L := by have hh := hg N (by omega) L hband; omega
  obtain ⟨e, he⟩ := PointedFiniteEnumeration.exists_equiv s hcard i
  let Y : Option (Fin s) → ℕ := fun j ↦ X (e j)
  let P := M.map (PhysicalWindowReindex.reindex X L e).toLinearMap
  obtain ⟨R, hRP, hrec, hdim, hproj⟩ := hreg (Option (Fin s)) (by simp) Y L hL P
  have hactive (v : Option (Fin s) × Fin (L + 1)) (hv : label Y L R v ≠ 0) : label Y L P v ≠ 0 := by
    intro hz
    apply hv
    ext u
    exact LinearMap.congr_fun hz ⟨u.val, hRP u.property⟩
  have hnoP : OffsetNonalignmentFrom.NoExactFrom Y L (fun v ↦ label Y L P v ≠ 0) none := by
    apply PhysicalWindowReindex.noExactFrom_reindex X L e M none
    simpa only [he] using hno
  have hnoR := OffsetNonalignmentFrom.mono Y L _ _ none hnoP hactive
  have hdimP : Module.finrank F₂ P = Module.finrank F₂ M :=
    PhysicalWindowReindex.finrank_image X L e M
  have hdimR : (η / 2) * L ≤ (Module.finrank F₂ R : ℝ) := by
    rw [hdimP] at hdim
    have hnonneg : 0 ≤ η * L := by positivity
    linarith only [hdense, hdim, hnonneg]
  have hinjP : Function.Injective ((projection Y L none).comp P.subtype) := by
    apply PhysicalWindowReindex.projection_image_injective X L e M none
    simpa only [he] using hinj
  have hh := hw N (by omega) L hband Y (fun j ↦ hX (e j)) R H hH hnoR hrec hdimR (hproj none hinjP)
  simpa only [Y, he] using hh

end PaperP1.DensePhysicalAnchorWitness
