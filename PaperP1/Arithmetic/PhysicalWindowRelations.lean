module

public import PaperP1.Arithmetic.EvenSquareClasses
public import PaperP1.Affine.Relations
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Physical even selections lift every actual effective window relation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PhysicalWindowRelations

open Finset PaperP1.Arithmetic PaperP1.Affine

local instance physicalWindowRelationTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {ι : Type*} [Fintype ι]

def code (X : ι → ℕ) (L : ℕ) : Submodule F₂ ((ι × Fin (L + 1)) → F₂) where
  carrier := {w | (∀ i, startVertexSum L (fun v ↦ w (i, v)) = 0) ∧
    (∑ i, vertexParityMap (X i) L (fun v ↦ w (i, v))) = 0}
  zero_mem' := by
    constructor
    · intro i
      exact map_zero (startVertexSum L)
    · change (∑ i, vertexParityMap (X i) L (0 : Fin (L + 1) → F₂)) = 0
      simp only [map_zero, sum_const_zero]
  add_mem' := by
    intro w z hw hz
    constructor
    · intro i
      change startVertexSum L ((fun v ↦ w (i, v)) + (fun v ↦ z (i, v))) = 0
      rw [map_add, hw.1 i, hz.1 i, add_zero]
    · change (∑ i, vertexParityMap (X i) L ((fun v ↦ w (i, v)) + (fun v ↦ z (i, v)))) = 0
      simp only [map_add, sum_add_distrib, hw.2, hz.2, add_zero]
  smul_mem' := by
    intro c w hw
    constructor
    · intro i
      change startVertexSum L (c • (fun v ↦ w (i, v))) = 0
      rw [map_smul, hw.1 i, smul_zero]
    · change (∑ i, vertexParityMap (X i) L (c • (fun v ↦ w (i, v)))) = 0
      simp only [map_smul]
      rw [← smul_sum, hw.2, smul_zero]

theorem mem_code (X : ι → ℕ) (L : ℕ) (w : (ι × Fin (L + 1)) → F₂) :
    w ∈ code X L ↔ (∀ i, startVertexSum L (fun v ↦ w (i, v)) = 0) ∧
      (∑ i, vertexParityMap (X i) L (fun v ↦ w (i, v))) = 0 := Iff.rfl

def localSelection (X : ι → ℕ) (L : ℕ) (i : ι) :
    code X L →ₗ[F₂] LinearMap.ker (startVertexSum L) where
  toFun w := ⟨fun v ↦ w.val (i, v), w.property.1 i⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def localValue (X : ι → ℕ) (L : ℕ) (i : ι) : code X L →ₗ[F₂] squareClassSpace (X i) L :=
  (evenSquareClassMap (X i) L).rangeRestrict.comp (localSelection X L i)

abbrev EffectiveKernel (X : ι → ℕ) (L : ℕ) :=
  LinearMap.ker (relationAddition (fun i ↦ squareClassSpace (X i) L))

def toEffective (X : ι → ℕ) (L : ℕ) : code X L →ₗ[F₂] EffectiveKernel X L :=
  (LinearMap.pi (localValue X L)).codRestrict _ (by
    intro w
    exact w.property.2)

theorem toEffective_surjective (X : ι → ℕ) (L : ℕ) : Function.Surjective (toEffective X L) := by
  intro r
  have hex : ∀ i, ∃ u : LinearMap.ker (startVertexSum L),
      evenSquareClassMap (X i) L u = (r.val i).val := fun i ↦ (r.val i).property
  choose u hu using hex
  let w : (ι × Fin (L + 1)) → F₂ := fun p ↦ (u p.1).val p.2
  have hw : w ∈ code X L := by
    constructor
    · intro i
      exact (u i).property
    · change (∑ i, evenSquareClassMap (X i) L (u i)) = 0
      simp only [hu]
      exact r.property
  refine ⟨⟨w, hw⟩, ?_⟩
  apply Subtype.ext
  funext i
  apply Subtype.ext
  exact hu i

def projection (X : ι → ℕ) (L : ℕ) (i : ι) : code X L →ₗ[F₂] (Fin (L + 1) → F₂) :=
  (LinearMap.pi fun v ↦ LinearMap.proj (i, v)).comp (code X L).subtype

def effectiveProjection (X : ι → ℕ) (L : ℕ) (i : ι) :
    EffectiveKernel X L →ₗ[F₂] squareClassSpace (X i) L :=
  (LinearMap.proj i).comp (EffectiveKernel X L).subtype

theorem localValue_range (X : ι → ℕ) (L : ℕ) (i : ι) :
    LinearMap.range (localValue X L i) = LinearMap.range (effectiveProjection X L i) := by
  ext s
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨toEffective X L w, rfl⟩
  · rintro ⟨r, rfl⟩
    obtain ⟨w, rfl⟩ := toEffective_surjective X L r
    exact ⟨w, rfl⟩

theorem projection_kernel_le (X : ι → ℕ) (L : ℕ) (i : ι) :
    LinearMap.ker (projection X L i) ≤ LinearMap.ker (localValue X L i) := by
  intro w hw
  have hselection : localSelection X L i w = 0 := Subtype.ext hw
  change (evenSquareClassMap (X i) L).rangeRestrict (localSelection X L i w) = 0
  rw [hselection, map_zero]

theorem effective_projection_rank_le (X : ι → ℕ) (L : ℕ) (i : ι) :
    Module.finrank F₂ (LinearMap.range (effectiveProjection X L i)) ≤
      Module.finrank F₂ (LinearMap.range (projection X L i)) := by
  have hlocal := LinearMap.finrank_range_add_finrank_ker (K := F₂)
    (V := code X L) (V₂ := squareClassSpace (X i) L) (localValue X L i)
  have hphysical := LinearMap.finrank_range_add_finrank_ker (K := F₂)
    (V := code X L) (V₂ := Fin (L + 1) → F₂) (projection X L i)
  have hker := Submodule.finrank_mono (projection_kernel_le X L i)
  rw [localValue_range] at hlocal
  omega

end PaperP1.PhysicalWindowRelations
