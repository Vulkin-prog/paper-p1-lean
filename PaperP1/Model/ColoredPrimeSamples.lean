module

public import PaperP1.Model.FiniteRademacher
public import PaperP1.Affine.StartSystem
public import PaperP1.Affine.Fourier
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Pi

/-! # A finite prime-sign model with common small signs and independent colored copies -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ColoredPrimeSamples

open PaperP1.Arithmetic PaperP1.Affine PaperP1.Model

local instance coloredPrimeSamplesTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

abbrev Sample (κ : Type*) (M : ℕ) := SampleSpace M × (κ → SampleSpace M)

instance sampleFintype {κ : Type*} [Fintype κ] (M : ℕ) : Fintype (Sample κ M) := by
  classical
  unfold Sample
  infer_instance

def glue {M : ℕ} (Y : ℕ) (common fresh : SampleSpace M) : SampleSpace M :=
  fun p ↦ if p.val.val ≤ Y then common p else fresh p

def select {κ : Type*} (M Y : ℕ) (color : κ) : Sample κ M →ₗ[F₂] SampleSpace M where
  toFun ω p := if p.val.val ≤ Y then ω.1 p else ω.2 color p
  map_add' ω η := by funext p; by_cases h : p.val.val ≤ Y <;> simp [h]
  map_smul' a ω := by funext p; by_cases h : p.val.val ≤ Y <;> simp [h]

def diagonal (κ : Type*) (M : ℕ) : SampleSpace M →ₗ[F₂] Sample κ M where
  toFun ω := (ω, fun _ ↦ ω)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem select_diagonal {κ : Type*} (M Y : ℕ) (color : κ) :
    (select M Y color).comp (diagonal κ M) = LinearMap.id := by
  ext ω p
  simp only [LinearMap.comp_apply, select, diagonal, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply]
  split_ifs <;> rfl

def start {κ : Type*} (M Y x L : ℕ) (color : κ) : Sample κ M →ₗ[F₂] (Fin L → F₂) :=
  (startSystem M x L).comp (select M Y color)

theorem start_diagonal {κ : Type*} (M Y x L : ℕ) (color : κ) :
    (start M Y x L color).comp (diagonal κ M) = startSystem M x L := by
  rw [start, LinearMap.comp_assoc, select_diagonal, LinearMap.comp_id]

theorem relationMap_comp {V W β : Type*} [AddCommGroup V] [Module F₂ V]
    [AddCommGroup W] [Module F₂ W] [Fintype β]
    (A : V →ₗ[F₂] (β → F₂)) (f : W →ₗ[F₂] V) :
    relationMap (A.comp f) = f.dualMap.comp (relationMap A) := by
  ext u w
  rfl

theorem start_relation_factor {κ : Type*} (M Y x L : ℕ) (color : κ) :
    relationMap (startSystem M x L) = (diagonal κ M).dualMap.comp (relationMap (start M Y x L color)) := by
  rw [← relationMap_comp, start_diagonal]

end PaperP1.ColoredPrimeSamples
