module

public import PaperP1.Algebra.BinaryIncidenceAugmentation
public import PaperP1.Algebra.ColumnDependencies

/-! # Actual loop and parallel-edge vectors in the binary incidence kernel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BinaryIncidenceShortVectors

open PaperP1.BinaryIncidenceAugmentation PaperP1.GreedyShortKernel

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {P E : Type*} [DecidableEq P]

def finsuppIncidence (left right : E → Option P) : (E →₀ ZMod 2) →ₗ[ZMod 2] (Option P → ZMod 2) :=
  Finsupp.linearCombination (ZMod 2) (fun e ↦ edgeColumn (left e) (right e))

theorem map_single (left right : E → Option P) (e : E) :
    finsuppIncidence left right (Finsupp.single e 1) = edgeColumn (left e) (right e) := by
  simp only [finsuppIncidence, Finsupp.linearCombination_single, one_smul]

theorem edgeColumn_self (a : Option P) : edgeColumn a a = 0 := by
  funext v
  by_cases hv : v = a
  · simp [edgeColumn, hv]
    decide
  · simp [edgeColumn, hv]

theorem edgeColumn_swap (a b : Option P) : edgeColumn a b = edgeColumn b a := by
  funext v
  exact add_comm _ _

theorem loop_short (left right : E → Option P) (e : E) (he : left e = right e) :
    HasShortVector (finsuppIncidence left right) {e} 1 := by
  apply ColumnDependencies.zero_column
  rw [map_single, he, edgeColumn_self]

theorem parallel_short [DecidableEq E] (left right : E → Option P) (e d : E) (hne : e ≠ d)
    (hparallel : (left e = left d ∧ right e = right d) ∨ (left e = right d ∧ right e = left d)) :
    HasShortVector (finsuppIncidence left right) {e, d} 2 := by
  apply ColumnDependencies.equal_columns _ e d hne
  rw [map_single, map_single]
  rcases hparallel with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · rw [hleft, hright]
  · rw [hleft, hright, edgeColumn_swap]

theorem finite_equivalence [Fintype E] (left right : E → Option P) :
    incidenceMap left right = (finsuppIncidence left right).comp
      (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) E).symm.toLinearMap :=
  (Finsupp.linearCombination_eq_fintype_linearCombination (ZMod 2)
    (fun e ↦ edgeColumn (left e) (right e))).symm

theorem finite_apply [Fintype E] (left right : E → Option P) (w : E →₀ ZMod 2) :
    finsuppIncidence left right w = incidenceMap left right
      ((Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) E) w) := by
  let e := Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) E
  have h := LinearMap.congr_fun (finite_equivalence left right)
    ((Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) E) w)
  change incidenceMap left right (e w) = finsuppIncidence left right (e.symm (e w)) at h
  rw [e.symm_apply_apply] at h
  exact h.symm

end PaperP1.BinaryIncidenceShortVectors
