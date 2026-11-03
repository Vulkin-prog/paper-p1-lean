module

public import PaperP1.Affine.DirectPartitions
public import PaperP1.Algebra.SubspaceFamilyRank

/-! # Distinct parts of an actual direct partition have disjoint sum-spaces -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DirectBlockDisjoint

open Finset PaperP1.Affine PaperP1.SubspaceFamilyRank

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [Fintype ι] [DecidableEq ι]

theorem single_addition (S : ι → Submodule 𝔽₂ U) (i : ι) (v : S i) :
    relationAddition S (Pi.single i v) = v.val := by
  rw [relationAddition_apply, sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [Pi.single_eq_of_ne hji]
  · simp

theorem pairwise_disjoint (S : ι → Submodule 𝔽₂ U)
    (hinj : Function.Injective (relationAddition S)) (i j : ι) (hij : i ≠ j) : Disjoint (S i) (S j) := by
  apply disjoint_iff.mpr
  apply bot_unique
  intro v hv
  let s : (k : ι) → S k := Pi.single i ⟨v, hv.1⟩
  let t : (k : ι) → S k := Pi.single j ⟨v, hv.2⟩
  have heq : s = t := hinj ((single_addition S i ⟨v, hv.1⟩).trans (single_addition S j ⟨v, hv.2⟩).symm)
  have h := congrArg (fun f : (k : ι) → S k ↦ (f i).val) heq
  change v = 0
  simpa only [s, t, Pi.single_eq_same, Pi.single_eq_of_ne hij, ZeroMemClass.coe_zero] using h

theorem partition_parts (S : ι → Submodule 𝔽₂ U) (P : Finpartition (univ : Finset ι))
    (hP : RelationDirectPartition S P) (C D : Finset ι) (hC : C ∈ P.parts) (hD : D ∈ P.parts)
    (hCD : C ≠ D) : Disjoint (span S C) (span S D) := by
  classical
  have hinj := (blockDirect_iff_addition_injective S P).mp ((relationDirect_iff_blockDirect S P).mp hP)
  have h := pairwise_disjoint (blockFamily S P) hinj (⟨C, hC⟩ : P.parts) (⟨D, hD⟩ : P.parts)
    (fun heq ↦ hCD (congrArg Subtype.val heq))
  simpa only [blockFamily, blockSpace_eq_iSup, span] using h

end PaperP1.DirectBlockDisjoint
