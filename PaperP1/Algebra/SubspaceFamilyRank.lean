module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Finset.Card
public import Lean.Elab.Tactic.Omega

/-! # Total and private ranks of finite families of actual subspaces -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SubspaceFamilyRank

open Finset

variable {K U ι : Type*} [DivisionRing K] [AddCommGroup U] [Module K U]
  [FiniteDimensional K U] [DecidableEq ι]
variable (S : ι → Submodule K U)

def span (A : Finset ι) : Submodule K U := ⨆ i : A, S i.val

def rank (A : Finset ι) : ℕ := Module.finrank K (span S A)

def privateRank (A : Finset ι) (i : ι) : ℕ := rank S A - rank S (A.erase i)

omit [FiniteDimensional K U] [DecidableEq ι] in
theorem span_mono {A B : Finset ι} (hAB : A ⊆ B) : span S A ≤ span S B := by
  refine iSup_le fun i ↦ ?_
  exact le_iSup_of_le (⟨i.val, hAB i.property⟩ : B) le_rfl

omit [DecidableEq ι] in
theorem rank_mono {A B : Finset ι} (hAB : A ⊆ B) : rank S A ≤ rank S B :=
  Submodule.finrank_mono (span_mono S hAB)

omit [FiniteDimensional K U] [DecidableEq ι] in
theorem span_empty : span S ∅ = ⊥ := by simp [span]

omit [FiniteDimensional K U] [DecidableEq ι] in
theorem rank_empty : rank S ∅ = 0 := by rw [rank, span_empty, finrank_bot]

omit [FiniteDimensional K U] in
theorem span_insert (i : ι) (A : Finset ι) : span S (insert i A) = S i ⊔ span S A := by
  apply le_antisymm
  · refine iSup_le fun j ↦ ?_
    obtain h | h := mem_insert.mp j.property
    · simpa only [h] using (le_sup_left : S i ≤ S i ⊔ span S A)
    · exact le_sup_of_le_right (le_iSup_of_le (⟨j.val, h⟩ : A) le_rfl)
  · refine sup_le (le_iSup_of_le (⟨i, mem_insert_self _ _⟩ : (insert i A : Finset ι)) le_rfl) ?_
    exact span_mono S (subset_insert i A)

theorem rank_insert_le (i : ι) (A : Finset ι) : rank S (insert i A) ≤ Module.finrank K (S i) + rank S A := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (S i) (span S A)
  rw [rank, span_insert]
  change Module.finrank K (S i ⊔ span S A : Submodule K U) ≤ Module.finrank K (S i) + Module.finrank K (span S A)
  omega

omit [FiniteDimensional K U] [DecidableEq ι] in
theorem local_le_span (A : Finset ι) {i : ι} (hi : i ∈ A) : S i ≤ span S A :=
  le_iSup_of_le (⟨i, hi⟩ : A) le_rfl

omit [DecidableEq ι] in
theorem local_rank_le (A : Finset ι) {i : ι} (hi : i ∈ A) : Module.finrank K (S i) ≤ rank S A :=
  Submodule.finrank_mono (local_le_span S A hi)

theorem rank_erase_add_private (A : Finset ι) (i : ι) : rank S (A.erase i) + privateRank S A i = rank S A := by
  have h := rank_mono S (erase_subset i A)
  unfold privateRank
  omega

theorem privateRank_le_local (A : Finset ι) {i : ι} (hi : i ∈ A) : privateRank S A i ≤ Module.finrank K (S i) := by
  have h := rank_insert_le S i (A.erase i)
  rw [insert_erase hi] at h
  unfold privateRank
  omega

theorem rank_le_sum (A : Finset ι) : rank S A ≤ ∑ i ∈ A, Module.finrank K (S i) := by
  induction A using Finset.induction_on with
  | empty => simp only [rank_empty, sum_empty, le_refl]
  | @insert i A hi ih =>
    rw [sum_insert hi]
    exact (rank_insert_le S i A).trans (Nat.add_le_add_left ih _)

theorem rank_le_card_mul (A : Finset ι) (L : ℕ) (hL : ∀ i ∈ A, Module.finrank K (S i) = L) :
    rank S A ≤ A.card * L := by
  calc
    _ ≤ ∑ i ∈ A, Module.finrank K (S i) := rank_le_sum S A
    _ = _ := by simp only [sum_congr rfl hL, sum_const, nsmul_eq_mul, Nat.cast_id]

omit [FiniteDimensional K U] in
theorem span_image {κ : Type*} (f : κ → ι) (A : Finset κ) :
    span S (A.image f) = span (fun i ↦ S (f i)) A := by
  apply le_antisymm
  · refine iSup_le fun i ↦ ?_
    obtain ⟨j, hj, hji⟩ := mem_image.mp i.property
    rw [← hji]
    exact local_le_span (fun k ↦ S (f k)) A hj
  · refine iSup_le fun j ↦ ?_
    exact local_le_span S (A.image f) (mem_image.mpr ⟨j.val, j.property, rfl⟩)

omit [FiniteDimensional K U] in
theorem rank_image {κ : Type*} (f : κ → ι) (A : Finset κ) :
    rank S (A.image f) = rank (fun i ↦ S (f i)) A := by rw [rank, span_image]; rfl

omit [FiniteDimensional K U] in
theorem rank_subtype_univ (A : Finset ι) : rank (fun i : A ↦ S i.val) univ = rank S A := by
  have himage : (univ : Finset A).image Subtype.val = A := by ext i; simp
  rw [← rank_image S (fun i : A ↦ i.val) univ, himage]

omit [FiniteDimensional K U] in
theorem rank_subtype_erase (A : Finset ι) (i : A) :
    rank (fun j : A ↦ S j.val) (univ.erase i) = rank S (A.erase i.val) := by
  classical
  have himage : (univ : Finset A).image Subtype.val = A := by ext j; simp
  rw [← rank_image S (fun j : A ↦ j.val) (univ.erase i), image_erase Subtype.val_injective, himage]

omit [FiniteDimensional K U] in
theorem privateRank_subtype (A : Finset ι) (i : A) :
    privateRank (fun j : A ↦ S j.val) univ i = privateRank S A i.val := by
  unfold privateRank
  rw [rank_subtype_univ, rank_subtype_erase]

end PaperP1.SubspaceFamilyRank
