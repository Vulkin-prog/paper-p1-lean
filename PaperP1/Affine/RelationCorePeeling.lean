module

public import PaperP1.Affine.RelationProjectionRank

/-! # Deleting small relation projections with an exact nullity budget -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelationCorePeeling

open Finset PaperP1.Affine PaperP1.RelationProjectionRank

variable {U κ : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq κ]
variable (S : κ → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

inductive Trace (k : ℕ) : Finset κ → Finset κ → Prop
  | stop (A : Finset κ) : Trace k A A
  | step {A B : Finset κ} (i : κ) (hi : i ∈ A) (hsmall : loss S A i ≤ k)
      (rest : Trace k (A.erase i) B) : Trace k A B

omit [∀ i, Fintype (S i)] in
theorem trace_subset {A B : Finset κ} {k : ℕ} (h : Trace S k A B) : B ⊆ A := by
  induction h with
  | stop A => exact Subset.rfl
  | @step A B i _ _ _ ih => exact ih.trans (erase_subset i A)

theorem trace_nullity_budget {A B : Finset κ} {k : ℕ} (h : Trace S k A B) :
    relativeNullityOn S A ≤ relativeNullityOn S B + k * (A.card - B.card) := by
  induction h with
  | stop A => simp
  | @step A B i hi hsmall rest ih =>
    have hBcard := card_le_card (trace_subset S rest)
    have hcard := card_erase_of_mem hi
    have hApos := card_pos.mpr ⟨i, hi⟩
    have hshift : A.card - B.card = (A.erase i).card - B.card + 1 := by omega
    have hdrop := erase_add_loss S A i
    rw [hshift, Nat.mul_add, Nat.mul_one]
    omega

omit [∀ i, Fintype (S i)] in
theorem exists_terminal_trace (A : Finset κ) (k : ℕ) :
    ∃ B, Trace S k A B ∧ ∀ i ∈ B, k < loss S B i := by
  classical
  refine Finset.strongInductionOn A ?_
  intro A ih
  by_cases heligible : ∃ i ∈ A, loss S A i ≤ k
  · obtain ⟨i, hi, hsmall⟩ := heligible
    obtain ⟨B, htrace, hstop⟩ := ih (A.erase i) (erase_ssubset hi)
    exact ⟨B, Trace.step i hi hsmall htrace, hstop⟩
  · refine ⟨A, Trace.stop A, ?_⟩
    intro i hi
    by_contra hnot
    exact heligible ⟨i, hi, by omega⟩

theorem exists_core (A : Finset κ) (k : ℕ) :
    ∃ B ⊆ A, relativeNullityOn S A ≤ relativeNullityOn S B + k * (A.card - B.card) ∧
      ∀ i ∈ B, k < loss S B i := by
  obtain ⟨B, htrace, hstop⟩ := exists_terminal_trace S A k
  exact ⟨B, trace_subset S htrace, trace_nullity_budget S htrace, hstop⟩

end PaperP1.RelationCorePeeling
