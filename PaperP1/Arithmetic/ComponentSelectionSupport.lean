module

public import PaperP1.Arithmetic.ShortBasisComponentStage

/-! # Literal physical supports of actual component-coordinate vectors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ComponentSelectionSupport

open Finset PaperP1.Arithmetic PaperP1.ComponentSelection PaperP1.LargePrimeOccurrences
  PaperP1.LargePrimeGraph PaperP1.ComponentProjectionInjectivity PaperP1.MediumPrimeColumns
  PaperP1.ShortBasisComponentStage

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance (x y L : ℕ) : DecidableEq (largePrimeGraph x y L).ConnectedComponent := Classical.decEq _

theorem selection_single (x y L : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (c : Q) (v : Occurrence L) :
    selection (largePrimeGraph x y L) Q (Pi.single c 1) v =
      if (largePrimeGraph x y L).connectedComponentMk v = c.val then 1 else 0 := by
  classical
  by_cases hv : (largePrimeGraph x y L).connectedComponentMk v = c.val
  · rw [ite_eq_left hv, selection_at_component _ Q _ c v hv]
    exact Pi.single_eq_same _ _
  · rw [ite_eq_right hv]
    by_cases hmem : (largePrimeGraph x y L).connectedComponentMk v ∈ Q
    · let d : Q := ⟨(largePrimeGraph x y L).connectedComponentMk v, hmem⟩
      rw [selection_at_component _ Q _ d v rfl]
      have hne : d ≠ c := fun h ↦ hv (congrArg Subtype.val h)
      exact Pi.single_eq_of_ne hne 1
    · exact selection_zero_of_outside _ _ hmem

def physicalSelection (x y L : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent) :
    (Q → F₂) →ₗ[F₂] (Occurrence L →₀ F₂) :=
  (Finsupp.linearEquivFunOnFinite F₂ F₂ (Occurrence L)).symm.toLinearMap.comp
    (selection (largePrimeGraph x y L) Q)

theorem physicalSelection_apply (x y L : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (w : Q → F₂) (v : Occurrence L) :
    physicalSelection x y L Q w v = selection (largePrimeGraph x y L) Q w v := rfl

theorem physical_single_support (x y L : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (c : Q) : (physicalSelection x y L Q (Pi.single c 1)).support =
      componentVertices (largePrimeGraph x y L) c.val := by
  classical
  apply Finset.ext
  intro v
  rw [Finsupp.mem_support_iff, physicalSelection_apply, selection_single, mem_componentVertices]
  by_cases hv : (largePrimeGraph x y L).connectedComponentMk v = c.val <;> simp [hv]

theorem retained_single_card (x y L z M : ℕ) (c : retainedComponents x y L z M) :
    (physicalSelection x y L (retainedComponents x y L z M) (Pi.single c 1)).support.card ≤ M := by
  rw [physical_single_support]
  exact retained_component_size x y L z M c.val c.property

end PaperP1.ComponentSelectionSupport
