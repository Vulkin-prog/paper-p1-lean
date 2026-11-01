module

public import PaperP1.Algebra.SubspaceFamilyRank
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-! # Constructing a terminal subfamily by deleting a large private rank -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateRankPeeling

open Finset PaperP1.SubspaceFamilyRank

variable {K U ι : Type*} [DivisionRing K] [AddCommGroup U] [Module K U]
  [FiniteDimensional K U] [DecidableEq ι]
variable (S : ι → Submodule K U)

inductive Trace (t : ℕ) : Finset ι → Finset ι → Prop
  | stop (A : Finset ι) : Trace t A A
  | step {A B : Finset ι} (i : ι) (hi : i ∈ A) (hprivate : t ≤ privateRank S A i)
      (rest : Trace t (A.erase i) B) : Trace t A B

omit [FiniteDimensional K U] in
theorem trace_subset {A B : Finset ι} {t : ℕ} (h : Trace S t A B) : B ⊆ A := by
  induction h with
  | stop A => exact Subset.rfl
  | @step A B i _ _ _ ih => exact ih.trans (erase_subset i A)

theorem trace_rank_budget {A B : Finset ι} {t : ℕ} (h : Trace S t A B) :
    t * (A.card - B.card) + rank S B ≤ rank S A := by
  induction h with
  | stop A => simp
  | @step A B i hi hprivate rest ih =>
    have hBcard := card_le_card (trace_subset S rest)
    have hcard := card_erase_of_mem hi
    have hApos := card_pos.mpr ⟨i, hi⟩
    have hshift : A.card - B.card = (A.erase i).card - B.card + 1 := by omega
    have hdrop := rank_erase_add_private S A i
    rw [hshift, Nat.mul_add, Nat.mul_one]
    omega

omit [FiniteDimensional K U] in
theorem exists_terminal_trace (A : Finset ι) (t : ℕ) :
    ∃ B, Trace S t A B ∧ ∀ i ∈ B, privateRank S B i < t := by
  classical
  refine Finset.strongInductionOn A ?_
  intro A ih
  by_cases heligible : ∃ i ∈ A, t ≤ privateRank S A i
  · obtain ⟨i, hi, hprivate⟩ := heligible
    obtain ⟨B, htrace, hstop⟩ := ih (A.erase i) (erase_ssubset hi)
    exact ⟨B, Trace.step i hi hprivate htrace, hstop⟩
  · refine ⟨A, Trace.stop A, ?_⟩
    intro i hi
    by_contra hnot
    exact heligible ⟨i, hi, by omega⟩

/-- Each deletion is charged against the actual decrease of total rank. -/
theorem exists_terminal (A : Finset ι) (t : ℕ) :
    ∃ B ⊆ A, t * (A.card - B.card) + rank S B ≤ rank S A ∧ ∀ i ∈ B, privateRank S B i < t := by
  obtain ⟨B, htrace, hstop⟩ := exists_terminal_trace S A t
  exact ⟨B, trace_subset S htrace, trace_rank_budget S htrace, hstop⟩

theorem trace_size_bound {A B : Finset ι} {t : ℕ} (ht : 0 < t) (htrace : Trace S t A B) :
    (A.card : ℝ) - rank S A / (t : ℝ) ≤ B.card ∧ rank S B ≤ rank S A := by
  have hB := trace_subset S htrace
  have hcost := trace_rank_budget S htrace
  have hBcard := card_le_card hB
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hcostNat : t * (A.card - B.card) ≤ rank S A := by omega
  have hcostR : (t : ℝ) * ((A.card : ℝ) - B.card) ≤ rank S A := by
    have h : ((t * (A.card - B.card) : ℕ) : ℝ) ≤ rank S A := by exact_mod_cast hcostNat
    simpa only [Nat.cast_mul, Nat.cast_sub hBcard] using h
  have hquot : (A.card : ℝ) - B.card ≤ rank S A / (t : ℝ) :=
    (le_div_iff₀ htR).mpr (by simpa only [mul_comm] using hcostR)
  exact ⟨by linarith, rank_mono S hB⟩

theorem exists_terminal_real (A : Finset ι) (t : ℕ) (ht : 0 < t) :
    ∃ B ⊆ A, (A.card : ℝ) - rank S A / (t : ℝ) ≤ B.card ∧ rank S B ≤ rank S A ∧
      ∀ i ∈ B, privateRank S B i < t := by
  obtain ⟨B, htrace, hstop⟩ := exists_terminal_trace S A t
  obtain ⟨hsize, hrank⟩ := trace_size_bound S ht htrace
  exact ⟨B, trace_subset S htrace, hsize, hrank, hstop⟩

end PaperP1.PrivateRankPeeling
