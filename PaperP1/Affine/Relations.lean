module

public import PaperP1.Affine.System
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Relations among a finite family of actual subspaces

The ambient vector space may be prime-exponent parity vectors or actual
linear characters. Local relations have already been factored out in each
subspace, before taking this addition kernel.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace PaperP1.Affine

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [Fintype ι]
variable (S : ι → Submodule 𝔽₂ U)

/-- Addition from the product of the effective subspaces. -/
def relationAddition : ((i : ι) → S i) →ₗ[𝔽₂] U where
  toFun := fun s => ∑ i, (s i).val
  map_add' := by intros; simp [Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.smul_sum]

@[simp]
theorem relationAddition_apply (s : (i : ι) → S i) :
    relationAddition S s = ∑ i, (s i).val := rfl

def HasFullSupport (s : (i : ι) → S i) : Prop := ∀ i, s i ≠ 0

def IsFullSupportRelation (s : (i : ι) → S i) : Prop :=
  HasFullSupport S s ∧ relationAddition S s = 0

end PaperP1.Affine
