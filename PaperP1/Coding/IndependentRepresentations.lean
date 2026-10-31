module

public import PaperP1.Coding.RecoveryLabelSupports
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! # Unordered representations by distinct independent labels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IndependentRepresentations

open Finset PaperP1.ZeroSumFreeRepresentations

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [DecidableEq W]

def independentRepresentations (K : Type*) [Field K] [Module K W]
    (S : Finset W) (j : ℕ) (α : W) : Finset (Finset W) := by
  classical
  exact (S.powersetCard j).filter fun A ↦ LinearIndepOn K id (↑A : Set W) ∧ (∑ a ∈ A, a) = α

theorem mem_independentRepresentations {S A : Finset W} {j : ℕ} {α : W} :
    A ∈ independentRepresentations K S j α ↔
      A ⊆ S ∧ A.card = j ∧ LinearIndepOn K id (↑A : Set W) ∧ (∑ a ∈ A, a) = α := by
  classical
  simp only [independentRepresentations, mem_filter, mem_powersetCard, and_assoc]

omit [DecidableEq W] in
theorem independent_zeroSumFree {A : Finset W} (hA : LinearIndepOn K id (↑A : Set W)) :
    ZeroSumFree A := by
  classical
  intro B hBA hzero
  apply eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hsum : (∑ a ∈ B, (1 : K) • id a) = 0 := by simpa only [one_smul, id_eq] using hzero
  have h := (linearIndepOn_iff'.mp hA) B (fun _ : W ↦ (1 : K)) hBA hsum b hb
  exact one_ne_zero h

theorem independentRepresentations_card_le (S : Finset W) (d t : ℕ)
    (hno : NoDisjointSums S d t) (j : ℕ) (hj : 1 ≤ j) (hjd : j ≤ d)
    (α : W) (hα : α ≠ 0) :
    (independentRepresentations K S j α).card ≤ j.factorial * (t - 1) ^ (j - 1) := by
  have hsub : independentRepresentations K S j α ⊆ representations S j α := by
    intro A hA
    obtain ⟨hAS, hcard, hLI, hsum⟩ := mem_independentRepresentations.mp hA
    exact mem_representations.mpr ⟨hAS, hcard, independent_zeroSumFree hLI, hsum⟩
  exact (card_le_card hsub).trans (representations_card_le S d t hno j hj hjd α hα)

theorem independentRepresentations_source_bound (S : Finset W) (d t : ℕ)
    (hno : NoDisjointSums S d t) (j : ℕ) (hj : 1 ≤ j) (hjd : j ≤ d)
    (α : W) (hα : α ≠ 0) :
    (independentRepresentations K S j α).card ≤ j.factorial * t ^ (j - 1) := by
  exact (independentRepresentations_card_le S d t hno j hj hjd α hα).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.sub_le t 1) (j - 1)))

end PaperP1.IndependentRepresentations
