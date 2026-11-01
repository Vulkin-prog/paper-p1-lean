module

public import PaperP1.Affine.RelationPartitions

/-! # Canonical partitions are preserved by coordinate-wise kernel equivalences -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CanonicalCoefficientTransport

open Finset PaperP1.Affine

variable {U V ι : Type*} [AddCommGroup U] [Module 𝔽₂ U]
  [AddCommGroup V] [Module 𝔽₂ V] [Fintype ι] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ U) (T : ι → Submodule 𝔽₂ V)
variable (e : ∀ i, S i ≃ₗ[𝔽₂] T i)

def coefficients (s : (i : ι) → S i) : (i : ι) → T i := fun i ↦ e i (s i)

omit [Fintype ι] in
theorem coefficients_restrict (C : Finset ι) (s : (i : ι) → S i) :
    coefficients S T e (restrictCoefficients S C s) =
      restrictCoefficients T C (coefficients S T e s) := by
  classical
  funext i
  by_cases hi : i ∈ C <;> simp [coefficients, restrictCoefficients, hi]

theorem directPartition_iff
    (hker : ∀ s : (i : ι) → S i,
      relationAddition S s = 0 ↔ relationAddition T (coefficients S T e s) = 0)
    (P : Finpartition (univ : Finset ι)) :
    RelationDirectPartition S P ↔ RelationDirectPartition T P := by
  classical
  constructor
  · intro hP t ht C hC
    let s : (i : ι) → S i := fun i ↦ (e i).symm (t i)
    have heq : coefficients S T e s = t := by funext i; exact (e i).apply_symm_apply _
    have hs : relationAddition S s = 0 := (hker s).mpr (by rwa [heq])
    have hCzero : relationAddition S (restrictCoefficients S C s) = 0 := by
      rw [relationAddition_restrictCoefficients]
      exact hP s hs C hC
    have htzero := (hker (restrictCoefficients S C s)).mp hCzero
    rw [coefficients_restrict, heq, relationAddition_restrictCoefficients] at htzero
    exact htzero
  · intro hP s hs C hC
    have ht := (hker s).mp hs
    have hCzero : relationAddition T (restrictCoefficients T C (coefficients S T e s)) = 0 := by
      rw [relationAddition_restrictCoefficients]
      exact hP _ ht C hC
    rw [← coefficients_restrict] at hCzero
    have hszero := (hker (restrictCoefficients S C s)).mpr hCzero
    rwa [relationAddition_restrictCoefficients] at hszero

theorem canonical_eq
    (hker : ∀ s : (i : ι) → S i,
      relationAddition S s = 0 ↔ relationAddition T (coefficients S T e s) = 0) :
    canonicalRelationPartition S = canonicalRelationPartition T := by
  apply le_antisymm
  · exact canonicalRelationPartition_le S _
      ((directPartition_iff S T e hker _).mpr (canonicalRelationPartition_respects T))
  · exact canonicalRelationPartition_le T _
      ((directPartition_iff S T e hker _).mp (canonicalRelationPartition_respects S))

end PaperP1.CanonicalCoefficientTransport
