module

public import PaperP1.Combinatorics.CoverGraphResolution

/-! # Independent binary coefficients on any chosen free graph components -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ComponentSelection

open Finset PaperP1.Arithmetic PaperP1.PinnedGraphResolution

variable {V : Type*}
variable (G : SimpleGraph V)

local instance componentSelectionPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance componentSelectionDecidableEq : DecidableEq G.ConnectedComponent := Classical.decEq _

def selection (Q : Finset G.ConnectedComponent) : (Q → F₂) →ₗ[F₂] (V → F₂) where
  toFun f v := if h : G.connectedComponentMk v ∈ Q then f ⟨G.connectedComponentMk v, h⟩ else 0
  map_add' f g := by ext v; dsimp; split_ifs <;> simp
  map_smul' a f := by ext v; dsimp; split_ifs <;> simp

theorem selection_at_out (Q : Finset G.ConnectedComponent) (f : Q → F₂) (c : Q) :
    selection G Q f c.val.out = f c := by
  have hcomp : G.connectedComponentMk c.val.out = c.val := c.val.out_eq
  simp only [selection, LinearMap.coe_mk, AddHom.coe_mk, hcomp, dite_eq_left c.property]

theorem selection_injective (Q : Finset G.ConnectedComponent) : Function.Injective (selection G Q) := by
  intro f g hfg
  funext c
  have h := congrFun hfg c.val.out
  simpa only [selection_at_out] using h

theorem selection_mem_graph {pins : Finset V} (Q : Finset G.ConnectedComponent)
    (hQ : ∀ c ∈ Q, ¬ComponentPinned G pins c) (f : Q → F₂) :
    selection G Q f ∈ PinnedGraphSpace G pins := by
  refine ⟨?_, ?_⟩
  · intro u v huv
    have heq := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj huv
    change (if h : G.connectedComponentMk u ∈ Q then f ⟨G.connectedComponentMk u, h⟩ else 0) =
      (if h : G.connectedComponentMk v ∈ Q then f ⟨G.connectedComponentMk v, h⟩ else 0)
    simp only [heq]
  · intro v hv
    have hnot : G.connectedComponentMk v ∉ Q := fun h ↦ hQ _ h ⟨v, hv, rfl⟩
    change (if h : G.connectedComponentMk v ∈ Q then f ⟨G.connectedComponentMk v, h⟩ else 0) = 0
    rw [dite_eq_right hnot]

theorem selection_zero_of_outside {Q : Finset G.ConnectedComponent} (f : Q → F₂) {v : V}
    (hv : G.connectedComponentMk v ∉ Q) : selection G Q f v = 0 := by
  change (if h : G.connectedComponentMk v ∈ Q then f ⟨G.connectedComponentMk v, h⟩ else 0) = 0
  rw [dite_eq_right hv]

theorem selection_supported {κ : Type*} (color : V → κ) (k : κ) (Q : Finset G.ConnectedComponent)
    (hQ : ∀ c ∈ Q, ∀ v ∈ c.supp, color v ≠ k) (f : Q → F₂) :
    ∀ v, color v = k → selection G Q f v = 0 := by
  intro v hv
  apply selection_zero_of_outside
  intro h
  exact hQ _ h v SimpleGraph.ConnectedComponent.connectedComponentMk_mem hv

theorem selection_mem_zeroed_rows [Fintype V] [DecidableEq V] {ι : Type*} {rows : ι → Finset V}
    (hrows : ∀ i, (rows i).card ≤ 3) {D : Finset V} (hD : CoverGraphResolution.IsCover rows D)
    (Q : Finset (CoverGraphResolution.graph rows D).ConnectedComponent)
    (hQ : ∀ c ∈ Q, ¬ComponentPinned (CoverGraphResolution.graph rows D) (CoverGraphResolution.pins rows D) c)
    (f : Q → F₂) : selection (CoverGraphResolution.graph rows D) Q f ∈
      CoordinateRestrictionRank.zeroed (CoverGraphResolution.rowSolutions rows) D := by
  rw [CoverGraphResolution.zeroed_eq_graph_space hrows hD]
  exact selection_mem_graph _ Q hQ f

end PaperP1.ComponentSelection
