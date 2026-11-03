module

public import PaperP1.Model.WeakTripleEffectiveRestriction
public import PaperP1.Arithmetic.PhysicalRelationSections
public import PaperP1.Arithmetic.PhysicalCoordinateErasure
public import PaperP1.Arithmetic.PhysicalSubspaceRegularization
public import PaperP1.Asymptotics.ExactUnitDeletionUniform

/-! # An unconditional large regularized physical subspace for every near-primitive triple

The exact-unit deletion, injective restriction and recovery losses are all paid
before applying any geometric count. No subspace or deletion set is enumerated.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NearPrimitivePhysicalRegularization

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations PaperP1.Model
  PaperP1.Model.InfiniteStarts PaperP1.ActivePhysicalPrimeGroups

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance codeAddCommGroup (I : Finset ℕ) (L : ℕ) : AddCommGroup (code (fun i : I ↦ i.val) L) := by
  with_unfolding_all
    exact Submodule.addCommGroup (R := F₂) (M := ((I × Fin (L + 1)) → F₂)) (code (fun i : I ↦ i.val) L)
local instance effectiveAddCommGroup (I : Finset ℕ) (L : ℕ) :
    AddCommGroup (EffectiveKernel (fun i : I ↦ i.val) L) := by
  with_unfolding_all
    exact Submodule.addCommGroup (R := F₂) (M := (i : I) → squareClassSpace i.val L)
      (EffectiveKernel (fun i : I ↦ i.val) L)
local instance effectiveSubspaceAddCommGroup (I : Finset ℕ) (L : ℕ)
    (R : Submodule F₂ (EffectiveKernel (fun i : I ↦ i.val) L)) : AddCommGroup R := by
  with_unfolding_all
    exact Submodule.addCommGroup (R := F₂) (M := EffectiveKernel (fun i : I ↦ i.val) L) R
local instance physicalAddCommGroup (I : Finset ℕ) (L : ℕ)
    (R : Submodule F₂ (code (fun i : I ↦ i.val) L)) : AddCommGroup R := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := code (fun i : I ↦ i.val) L) R

theorem uniform_subspace (C η θ : ℝ) (hη : 0 < η) (hθ : 0 ≤ θ) (hθsmall : θ < η / 100) :
    ∃ t : ℕ, 2 ≤ t ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ I : Finset ℕ, I.card = 3 → I ⊆ dyadicBlock N →
      η * ((L + 1 : ℕ) : ℝ) ≤ (runRelativeNullity L I : ℝ) →
      (∀ x ∈ I, ∀ y ∈ I, x ≠ y →
        (Module.finrank F₂ ↥(squareClassSpace x L ⊓ squareClassSpace y L) : ℝ) ≤ θ * ((L + 1 : ℕ) : ℝ)) →
      ∃ M : Submodule F₂ (code (fun i : I ↦ i.val) L),
        DisjointRecoverySubspace.NoDisjointRecovery (CoordinateForms.coordinateFamily (code (fun i : I ↦ i.val) L)) M 2 t ∧
        (η / 4) * L ≤ (Module.finrank F₂ M : ℝ) ∧
        (∀ i, Function.Injective ((projection (fun j : I ↦ j.val) L i).comp M.subtype)) ∧
        OffsetNonalignmentOn.NoExactOn (fun i : I ↦ i.val) L
          (fun v ↦ label (fun i : I ↦ i.val) L M v ≠ 0) := by
  obtain ⟨t, ht, hreg⟩ := PhysicalSubspaceRegularization.uniform_subspace η hη
  obtain ⟨ND, _hND, hd⟩ := ExactUnitDeletionUniform.uniform_deletion C θ hθ
  obtain ⟨B₀, hB₀⟩ := exists_nat_gt (144 / η)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C (B₀ + 1)
  refine ⟨t, ht, 3 + ND + NG, by omega, ?_⟩
  intro N hN L hband I hcard hIG hdense hweak
  classical
  have hgeom := hg N (by omega) L hband
  have hL : 1 ≤ L := by omega
  let X : I → ℕ := fun i ↦ i.val
  have hι : Fintype.card I ≤ 3 := by simp only [Fintype.card_coe, hcard, le_refl]
  have hX (i : I) : X i ∈ dyadicBlock N := hIG i.property
  have hweakX (i j : I) (hij : i ≠ j) :
      (Module.finrank F₂ ↥(squareClassSpace (X i) L ⊓ squareClassSpace (X j) L) : ℝ) ≤ θ * ((L + 1 : ℕ) : ℝ) :=
    hweak i.val i.property j.val j.property (fun he ↦ hij (Subtype.ext he))
  obtain ⟨D, hD, hnoD⟩ := hd N (by omega) L hband I hι X hX hweakX
  obtain ⟨R, hR, hinjR⟩ := WeakTripleEffectiveRestriction.exists_restriction I L hcard
    (θ * ((L + 1 : ℕ) : ℝ)) hweak
  obtain ⟨P₀, hP₀, hinj₀⟩ := PhysicalRelationSections.section_subspace X L R hinjR
  obtain ⟨P₁, _hP₁le, hcostD, hzero, hinj₁⟩ := PhysicalCoordinateErasure.exists_erasure X L P₀ hinj₀ D
  obtain ⟨M, hMle, hrec, hMdim, hinjM⟩ := hreg I hι X L hL P₁ hinj₁
  have hMzero (u : M) (v : I × Fin (L + 1)) (hv : v ∈ D) : u.val.val v = 0 :=
    hzero ⟨u.val, hMle u.property⟩ v hv
  have hno := PhysicalCoordinateErasure.active_no_exact X L M D hMzero hnoD
  have hmacro : 144 ≤ η * ((L + 1 : ℕ) : ℝ) := by
    have hh := (div_lt_iff₀ hη).mp hB₀
    have hBR : (B₀ : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast (show B₀ ≤ L + 1 by omega)
    have hm := mul_le_mul_of_nonneg_left hBR hη.le
    nlinarith only [hh, hm]
  have hθ21 : 21 * θ ≤ η / 4 := by linarith only [hθsmall, hη]
  have hθB := mul_le_mul_of_nonneg_right hθ21 (Nat.cast_nonneg (α := ℝ) (L + 1))
  have hLB : (L : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ L
  have hηLB := mul_le_mul_of_nonneg_left hLB hη.le
  have hcostDR : (Module.finrank F₂ P₀ : ℝ) ≤ (D.card : ℝ) + Module.finrank F₂ P₁ := by exact_mod_cast hcostD
  rw [hP₀] at hcostDR
  have hdim : (η / 4) * L ≤ (Module.finrank F₂ M : ℝ) := by
    nlinarith only [hdense, hR, hD, hcostDR, hMdim, hmacro, hθB, hηLB]
  exact ⟨M, hrec, hdim, hinjM, hno⟩

end PaperP1.NearPrimitivePhysicalRegularization
