module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # A relation above a prescribed effective source space projects injectively to each target -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetKernel

variable {K U : Type*} [Field K] [AddCommGroup U] [Module K U]

def addition (W Y Z : Submodule K U) : (W × Y × Z) →ₗ[K] U where
  toFun p := (p.1 : U) + (p.2.1 : U) + (p.2.2 : U)
  map_add' _ _ := by simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add]; abel
  map_smul' _ _ := by simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_add, RingHom.id_apply]

abbrev Kernel (W Y Z : Submodule K U) := LinearMap.ker (addition W Y Z)

def leftProjection (W Y Z : Submodule K U) : Kernel W Y Z →ₗ[K] Y :=
  (LinearMap.fst K Y Z).comp ((LinearMap.snd K W (Y × Z)).comp (Kernel W Y Z).subtype)

def rightProjection (W Y Z : Submodule K U) : Kernel W Y Z →ₗ[K] Z :=
  (LinearMap.snd K Y Z).comp ((LinearMap.snd K W (Y × Z)).comp (Kernel W Y Z).subtype)

theorem range_addition (W Y Z : Submodule K U) :
    LinearMap.range (addition W Y Z) = W ⊔ (Y ⊔ Z) := by
  apply le_antisymm
  · rintro u ⟨p, rfl⟩
    have hW : W ≤ W ⊔ (Y ⊔ Z) := le_sup_left
    have hY : Y ≤ W ⊔ (Y ⊔ Z) := le_sup_left.trans le_sup_right
    have hZ : Z ≤ W ⊔ (Y ⊔ Z) := le_sup_right.trans le_sup_right
    exact (W ⊔ (Y ⊔ Z)).add_mem
      ((W ⊔ (Y ⊔ Z)).add_mem (hW p.1.property) (hY p.2.1.property))
      (hZ p.2.2.property)
  · refine sup_le ?_ (sup_le ?_ ?_)
    · intro w hw
      exact ⟨(⟨w, hw⟩, 0, 0), by simp only [addition, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_zero, add_zero]⟩
    · intro y hy
      exact ⟨(0, ⟨y, hy⟩, 0), by simp only [addition, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_zero, zero_add, add_zero]⟩
    · intro z hz
      exact ⟨(0, 0, ⟨z, hz⟩), by simp only [addition, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_zero, zero_add]⟩

theorem left_projection_injective (W Y Z : Submodule K U) (hWZ : Disjoint W Z) :
    Function.Injective (leftProjection W Y Z) := by
  have hz : ∀ r : Kernel W Y Z, leftProjection W Y Z r = 0 → r = 0 := by
    intro r hr
    have hy : r.val.2.1 = 0 := hr
    have hsum : (r.val.1 : U) + (r.val.2.2 : U) = 0 := by
      have h := r.property
      change (r.val.1 : U) + (r.val.2.1 : U) + (r.val.2.2 : U) = 0 at h
      simpa only [hy, Submodule.coe_zero, add_zero] using h
    have hwZ : (r.val.1 : U) ∈ Z := by
      rw [eq_neg_of_add_eq_zero_left hsum]
      exact Z.neg_mem r.val.2.2.property
    have hw : r.val.1 = 0 := Submodule.eq_zero_of_coe_mem_of_disjoint hWZ hwZ
    have hz : r.val.2.2 = 0 := by
      apply Subtype.ext
      simpa only [hw, Submodule.coe_zero, zero_add] using hsum
    apply Subtype.ext
    exact Prod.ext hw (Prod.ext hy hz)
  intro r s hrs
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, hrs, sub_self]

theorem right_projection_injective (W Y Z : Submodule K U) (hWY : Disjoint W Y) :
    Function.Injective (rightProjection W Y Z) := by
  have hz : ∀ r : Kernel W Y Z, rightProjection W Y Z r = 0 → r = 0 := by
    intro r hr
    have hz : r.val.2.2 = 0 := hr
    have hsum : (r.val.1 : U) + (r.val.2.1 : U) = 0 := by
      have h := r.property
      change (r.val.1 : U) + (r.val.2.1 : U) + (r.val.2.2 : U) = 0 at h
      simpa only [hz, Submodule.coe_zero, add_zero] using h
    have hwY : (r.val.1 : U) ∈ Y := by
      rw [eq_neg_of_add_eq_zero_left hsum]
      exact Y.neg_mem r.val.2.1.property
    have hw : r.val.1 = 0 := Submodule.eq_zero_of_coe_mem_of_disjoint hWY hwY
    have hy : r.val.2.1 = 0 := by
      apply Subtype.ext
      simpa only [hw, Submodule.coe_zero, zero_add] using hsum
    apply Subtype.ext
    exact Prod.ext hw (Prod.ext hy hz)
  intro r s hrs
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, hrs, sub_self]

variable (W Y Z : Submodule K U) [FiniteDimensional K W] [FiniteDimensional K Y]
  [FiniteDimensional K Z]

theorem dimension_identity :
    Module.finrank K W + Module.finrank K Y + Module.finrank K Z =
      Module.finrank K (W ⊔ (Y ⊔ Z) : Submodule K U) + Module.finrank K (Kernel W Y Z) := by
  have h := (addition W Y Z).finrank_range_add_finrank_ker
  rw [range_addition, Module.finrank_prod, Module.finrank_prod] at h
  simpa only [add_assoc] using h.symm

theorem dimension_deficit :
    Module.finrank K (Kernel W Y Z) =
      Module.finrank K W + Module.finrank K Y + Module.finrank K Z -
        Module.finrank K (W ⊔ (Y ⊔ Z) : Submodule K U) := by
  have h := dimension_identity W Y Z
  omega

omit [FiniteDimensional K W] [FiniteDimensional K Z] in
theorem dimension_le_left (hWZ : Disjoint W Z) :
    Module.finrank K (Kernel W Y Z) ≤ Module.finrank K Y :=
  LinearMap.finrank_le_finrank_of_injective (left_projection_injective W Y Z hWZ)

omit [FiniteDimensional K W] [FiniteDimensional K Y] in
theorem dimension_le_right (hWY : Disjoint W Y) :
    Module.finrank K (Kernel W Y Z) ≤ Module.finrank K Z :=
  LinearMap.finrank_le_finrank_of_injective (right_projection_injective W Y Z hWY)

omit [FiniteDimensional K W] in
theorem dimension_le_min (hWY : Disjoint W Y) (hWZ : Disjoint W Z) :
    Module.finrank K (Kernel W Y Z) ≤ min (Module.finrank K Y) (Module.finrank K Z) :=
  le_min (dimension_le_left W Y Z hWZ) (dimension_le_right W Y Z hWY)

end PaperP1.TwoTargetKernel
