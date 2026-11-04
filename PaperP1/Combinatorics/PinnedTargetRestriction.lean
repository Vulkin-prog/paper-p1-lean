module

public import PaperP1.Combinatorics.PinnedGraphResolution

/-! # Only unpinned components meeting the actual target contribute to its image rank -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PinnedTargetRestriction

open Finset PaperP1.Arithmetic PaperP1.PinnedGraphResolution

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {V : Type*} [Fintype V] [DecidableEq V]

def components (G : SimpleGraph V) (pins T : Finset V) : Finset G.ConnectedComponent := by
  classical
  exact (unpinnedComponents G pins).filter fun c ↦ ∃ v ∈ T, G.connectedComponentMk v = c

theorem mem_components (G : SimpleGraph V) (pins T : Finset V) (c : G.ConnectedComponent) :
    c ∈ components G pins T ↔ ¬ComponentPinned G pins c ∧ ∃ v ∈ T, G.connectedComponentMk v = c := by
  classical
  simp only [components, mem_filter, mem_unpinnedComponents]

def restriction (G : SimpleGraph V) (pins T : Finset V) : PinnedGraphSpace G pins →ₗ[F₂] (T → F₂) where
  toFun f v := f.val v.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def extend (G : SimpleGraph V) (pins T : Finset V) (a : components G pins T → F₂) : T → F₂ := by
  classical
  exact fun v ↦ if hp : ComponentPinned G pins (G.connectedComponentMk v.val) then 0 else
    a ⟨G.connectedComponentMk v.val, (mem_components G pins T _).mpr ⟨hp, v.val, v.property, rfl⟩⟩

def extension (G : SimpleGraph V) (pins T : Finset V) : (components G pins T → F₂) →ₗ[F₂] (T → F₂) where
  toFun := extend G pins T
  map_add' a b := by
    classical
    funext v
    by_cases hp : ComponentPinned G pins (G.connectedComponentMk v.val) <;> simp [extend, hp]
  map_smul' a b := by
    classical
    funext v
    by_cases hp : ComponentPinned G pins (G.connectedComponentMk v.val) <;> simp [extend, hp]

def componentValues (G : SimpleGraph V) (pins T : Finset V) (f : PinnedGraphSpace G pins) :
    components G pins T → F₂ := fun c ↦ f.val c.val.out

theorem extension_componentValues (G : SimpleGraph V) (pins T : Finset V) (f : PinnedGraphSpace G pins) :
    extension G pins T (componentValues G pins T f) = restriction G pins T f := by
  classical
  funext v
  change extend G pins T (componentValues G pins T f) v = f.val v.val
  by_cases hp : ComponentPinned G pins (G.connectedComponentMk v.val)
  · rw [extend, dite_eq_left hp]
    exact (eq_zero_of_componentPinned G f hp).symm
  · rw [extend, dite_eq_right hp]
    change f.val (G.connectedComponentMk v.val).out = f.val v.val
    apply eq_of_connectedComponentMk_eq G f
    exact (G.connectedComponentMk v.val).out_eq

theorem finrank_restriction_le (G : SimpleGraph V) (pins T : Finset V) :
    Module.finrank F₂ (LinearMap.range (restriction G pins T)) ≤ (components G pins T).card := by
  classical
  have hsub : LinearMap.range (restriction G pins T) ≤ LinearMap.range (extension G pins T) := by
    rintro _ ⟨f, rfl⟩
    exact ⟨componentValues G pins T f, extension_componentValues G pins T f⟩
  calc
    _ ≤ Module.finrank F₂ (LinearMap.range (extension G pins T)) := Submodule.finrank_mono hsub
    _ ≤ Module.finrank F₂ (components G pins T → F₂) := LinearMap.finrank_range_le _
    _ = _ := by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

def targets {ι : Type*} [Fintype ι] (e : ι → V) : Finset V := by
  classical
  exact univ.image e

def restrictionOn {ι : Type*} (G : SimpleGraph V) (pins : Finset V) (e : ι → V) :
    PinnedGraphSpace G pins →ₗ[F₂] (ι → F₂) where
  toFun f i := f.val (e i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def pullback {ι : Type*} [Fintype ι] (e : ι → V) : (targets e → F₂) →ₗ[F₂] (ι → F₂) where
  toFun a i := a ⟨e i, by
    classical
    exact mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_restrictionOn_le {ι : Type*} [Fintype ι]
    (G : SimpleGraph V) (pins : Finset V) (e : ι → V) :
    Module.finrank F₂ (LinearMap.range (restrictionOn G pins e)) ≤ (components G pins (targets e)).card := by
  have he : restrictionOn G pins e = (pullback e).comp (restriction G pins (targets e)) := rfl
  rw [he, LinearMap.range_comp]
  exact (Submodule.finrank_map_le _ _).trans (finrank_restriction_le G pins (targets e))

theorem components_pin_cover (G : SimpleGraph V) (pins T U : Finset V) (hU : U ⊆ T ∪ pins) :
    components G pins U ⊆ components G pins T := by
  classical
  intro c hc
  obtain ⟨hfree, v, hv, he⟩ := (mem_components G pins U c).mp hc
  rcases mem_union.mp (hU hv) with hvT | hvP
  · exact (mem_components G pins T c).mpr ⟨hfree, v, hvT, he⟩
  · exact False.elim (hfree ⟨v, hvP, he⟩)

theorem finrank_restrictionOn_le_of_pins {ι : Type*} [Fintype ι]
    (G : SimpleGraph V) (pins T : Finset V) (e : ι → V) (hcover : ∀ i, e i ∈ T ∪ pins) :
    Module.finrank F₂ (LinearMap.range (restrictionOn G pins e)) ≤ (components G pins T).card := by
  apply (finrank_restrictionOn_le G pins e).trans
  apply card_le_card
  apply components_pin_cover G pins T (targets e)
  intro v hv
  obtain ⟨i, _hi, rfl⟩ := mem_image.mp hv
  exact hcover i

end PaperP1.PinnedTargetRestriction
