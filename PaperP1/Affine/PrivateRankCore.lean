module

public import PaperP1.Algebra.PrivateRankPeeling
public import PaperP1.Affine.ComponentRankDensity

/-! # A constructed terminal subfamily and an actual dense canonical component -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateRankCore

open Finset PaperP1.Affine PaperP1.SubspaceFamilyRank PaperP1.PrivateRankPeeling

variable {U ι : Type*} [AddCommGroup U] [Module 𝔽₂ U] [FiniteDimensional 𝔽₂ U] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

def density (A : Finset ι) (t : ℕ) : ℝ := (rank S A : ℝ) / ((A.card : ℝ) - rank S A / (t : ℝ))

def DenseConclusion (A B : Finset ι) (L t : ℕ) : Prop :=
  (0 < (A.card : ℝ) - rank S A / (t : ℝ)) →
    ∃ C : (canonicalRelationPartition (fun i : B ↦ S i.val)).parts,
      (rank (fun i : B ↦ S i.val) C.val : ℝ) / C.val.card ≤ density S A t ∧
      (L : ℝ) / density S A t ≤ C.val.card ∧
      (L : ℝ) ^ 2 / density S A t - L ≤ relativeNullityOn (fun i : B ↦ S i.val) C.val

theorem exists_core (A : Finset ι) (L t : ℕ) (ht : 0 < t) (htL : t ≤ L)
    (hL : ∀ i ∈ A, Module.finrank 𝔽₂ (S i) = L) :
    ∃ B ⊆ A, (A.card : ℝ) - rank S A / (t : ℝ) ≤ B.card ∧ rank S B ≤ rank S A ∧
      (∀ i ∈ B, privateRank S B i < t) ∧ DenseConclusion S A B L t := by
  classical
  obtain ⟨B, hB, hcard, hrank, hstop⟩ := exists_terminal_real S A t ht
  refine ⟨B, hB, hcard, hrank, hstop, ?_⟩
  intro hpositive
  have hBpos : (0 : ℝ) < B.card := hpositive.trans_le hcard
  have hBnonempty : B.Nonempty := card_pos.mp (by exact_mod_cast hBpos)
  obtain ⟨i, hi⟩ := hBnonempty
  have hlocal := local_rank_le S B hi
  rw [hL i (hB hi)] at hlocal
  have hRpos : (0 : ℝ) < rank S A := by exact_mod_cast (by omega : 0 < rank S A)
  have hD : 0 < density S A t := div_pos hRpos hpositive
  have hDb : density S A t * ((A.card : ℝ) - rank S A / (t : ℝ)) = rank S A := by
    exact div_mul_cancel₀ _ hpositive.ne'
  have hbound : (rank S B : ℝ) ≤ density S A t * B.card := by
    have hrankR : (rank S B : ℝ) ≤ rank S A := by exact_mod_cast hrank
    calc
      _ ≤ (rank S A : ℝ) := hrankR
      _ = density S A t * ((A.card : ℝ) - rank S A / (t : ℝ)) := hDb.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hcard hD.le
  let T : B → Submodule 𝔽₂ U := fun j ↦ S j.val
  let P := canonicalRelationPartition T
  have hP : RelationDirectPartition T P := canonicalRelationPartition_respects T
  have hT : (rank T univ : ℝ) ≤ density S A t * Fintype.card B := by
    simpa only [T, rank_subtype_univ, Fintype.card_coe] using hbound
  obtain ⟨C, hC⟩ := ComponentRankDensity.exists_part_density T P hP (density S A t) ⟨⟨i, hi⟩⟩ hT
  have hLT (j : B) : Module.finrank 𝔽₂ (T j) = L := hL j.val (hB j.property)
  exact ⟨C, ComponentRankDensity.dense_part_bounds T P C L hLT (density S A t) hD hC⟩

end PaperP1.PrivateRankCore
