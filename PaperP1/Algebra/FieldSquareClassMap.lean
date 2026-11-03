module

public import PaperP1.Algebra.FieldSquareClasses
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Module.Submodule.Ker

/-! # The actual linear map on square classes induced by a field embedding -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FieldSquareClassMap

open PaperP1.FieldSquareClasses

variable {K E : Type*} [Field K] [Field E]

def unitsAddMap (φ : K →+* E) : Additive Kˣ →+ Additive Eˣ :=
  (Units.map φ.toMonoidHom).toAdditive

theorem doubles_le (φ : K →+* E) : doubles K ≤ (doubles E).comap (unitsAddMap φ) := by
  rintro z ⟨u, hu⟩
  change ∃ v : Additive Eˣ, 2 • v = unitsAddMap φ z
  refine ⟨unitsAddMap φ u, ?_⟩
  rw [← map_nsmul]
  exact congrArg (unitsAddMap φ) hu

def map (φ : K →+* E) : Classes K →ₗ[ZMod 2] Classes E :=
  (QuotientAddGroup.map (doubles K) (doubles E) (unitsAddMap φ) (doubles_le φ)).toZModLinearMap 2

theorem map_unitClass (φ : K →+* E) (u : Kˣ) :
    map φ (unitClass u) = unitClass (Units.map φ.toMonoidHom u) := rfl

theorem map_ofNonzero (φ : K →+* E) (a : K) (ha : a ≠ 0) :
    map φ (ofNonzero a ha) = ofNonzero (φ a) ((map_ne_zero φ).mpr ha) := by
  change unitClass (Units.map φ.toMonoidHom (Units.mk0 a ha)) = _
  apply congrArg unitClass
  apply Units.ext
  rfl

theorem mem_kernel_iff (φ : K →+* E) (a : K) (ha : a ≠ 0) :
    ofNonzero a ha ∈ LinearMap.ker (map φ) ↔ IsSquare (φ a) := by
  rw [LinearMap.mem_ker, map_ofNonzero, ofNonzero_zero_iff]

theorem exists_representative (z : Classes K) : ∃ a : K, ∃ ha : a ≠ 0, ofNonzero a ha = z := by
  induction z using Quotient.inductionOn with
  | _ u =>
    refine ⟨(u.toMul : K), Units.ne_zero _, ?_⟩
    change unitClass (Units.mk0 (u.toMul : K) (Units.ne_zero _)) = unitClass u.toMul
    apply congrArg unitClass
    apply Units.ext
    rfl

end PaperP1.FieldSquareClassMap
