module

public import PaperP1.Combinatorics.FinitePolymerTail

/-! # Subtract the empty collection and exactly one distinguished component before taking the exponential majorant -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FinitePolymerRemainder

open Finset

variable {ι : Type*} [DecidableEq ι]

def remainder (A E : Finset ι) : Finset (Finset ι) := A.powerset \ insert ∅ (E.image singleton)

theorem remainder_eq (w : ι → ℝ) (A E : Finset ι) (hEA : E ⊆ A) :
    (∑ P ∈ remainder A E, ∏ x ∈ P, w x) = (∏ x ∈ A, (1 + w x)) - 1 - ∑ x ∈ E, w x := by
  classical
  have hsub : insert ∅ (E.image singleton) ⊆ A.powerset := by
    intro P hP
    rcases mem_insert.mp hP with rfl | hP
    · simp
    · obtain ⟨x, hx, rfl⟩ := mem_image.mp hP
      exact mem_powerset.mpr (singleton_subset_iff.mpr (hEA hx))
  have hlow : (∑ P ∈ insert ∅ (E.image singleton), ∏ x ∈ P, w x) = 1 + ∑ x ∈ E, w x := by
    rw [sum_insert (by simp), sum_image (fun x _ y _ h ↦ by simpa only [singleton_inj] using h)]
    simp only [prod_empty, prod_singleton]
  have h := sum_sdiff hsub (f := fun P ↦ ∏ x ∈ P, w x)
  rw [hlow, ← prod_one_add A] at h
  change (∑ P ∈ remainder A E, ∏ x ∈ P, w x) + (1 + ∑ x ∈ E, w x) = _ at h
  linarith only [h]

theorem covered_bound {V : Type*} [DecidableEq V] (F : Finset (Finset V))
    (A E : Finset (Finset V)) (hEA : E ⊆ A) (v w : Finset V → ℝ) (hw : ∀ C, 0 ≤ w C)
    (hcover : ∀ D ∈ F, ∃ P ⊆ A, P.biUnion id = D ∧ P.Nonempty ∧
      (∀ e ∈ E, P ≠ {e}) ∧ v D ≤ ∏ C ∈ P, w C) :
    (∑ D ∈ F, v D) ≤ Real.exp (∑ C ∈ A, w C) - 1 - ∑ e ∈ E, w e := by
  classical
  let select (D : Finset V) := if h : D ∈ F then Classical.choose (hcover D h) else ∅
  have hs (D : Finset V) (hD : D ∈ F) : select D ⊆ A ∧ (select D).biUnion id = D ∧
      (select D).Nonempty ∧ (∀ e ∈ E, select D ≠ {e}) ∧ v D ≤ ∏ C ∈ select D, w C := by
    dsimp [select]
    rw [dite_eq_left hD]
    exact Classical.choose_spec (hcover D hD)
  have hinj : Set.InjOn select (↑F : Set (Finset V)) := by
    intro D hD E hE heq
    have hu := congrArg (fun P : Finset (Finset V) ↦ P.biUnion id) heq
    rwa [(hs D hD).2.1, (hs E hE).2.1] at hu
  have hsub : F.image select ⊆ remainder A E := by
    intro P hP
    obtain ⟨D, hD, rfl⟩ := mem_image.mp hP
    refine mem_sdiff.mpr ⟨mem_powerset.mpr (hs D hD).1, ?_⟩
    intro hlow
    rcases mem_insert.mp hlow with heq | heq
    · exact (hs D hD).2.2.1.ne_empty heq
    · obtain ⟨e, he, heq⟩ := mem_image.mp heq
      exact (hs D hD).2.2.2.1 e he heq.symm
  calc
    _ ≤ ∑ D ∈ F, ∏ C ∈ select D, w C := sum_le_sum fun D hD ↦ (hs D hD).2.2.2.2
    _ = ∑ P ∈ F.image select, ∏ C ∈ P, w C := (sum_image (f := fun P : Finset (Finset V) ↦ ∏ C ∈ P, w C) hinj).symm
    _ ≤ ∑ P ∈ remainder A E, ∏ C ∈ P, w C := sum_le_sum_of_subset_of_nonneg hsub
      (fun P _ _ ↦ prod_nonneg fun C _ ↦ hw C)
    _ = (∏ C ∈ A, (1 + w C)) - 1 - ∑ e ∈ E, w e := remainder_eq w A E hEA
    _ ≤ _ := by have h := Real.prod_one_add_le_exp_sum A hw; linarith only [h]

theorem exponential_error (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.exp (a + b) - 1 - a ≤ b + ((a + b) ^ 2 / 2) * Real.exp (a + b) := by
  let x := a + b
  have hx : 0 ≤ x := add_nonneg ha hb
  have hTaylor := PaperP1.BanachFactorialRemainder.norm_exp_sub_partial_le (x : ℝ) 2
  have hpart : (∑ j ∈ range 2, ((j.factorial : ℝ)⁻¹) • x ^ j) = 1 + x := by norm_num [sum_range_succ]
  rw [hpart, ← Real.exp_eq_exp_ℝ] at hTaylor
  simp only [Real.norm_eq_abs, abs_of_nonneg hx] at hTaylor
  norm_num only [Nat.factorial, Nat.cast_one, Nat.cast_ofNat, mul_one] at hTaylor
  have hle := le_abs_self (Real.exp x - (1 + x))
  change Real.exp x - 1 - a ≤ b + (x ^ 2 / 2) * Real.exp x
  dsimp only [x] at hTaylor hle ⊢
  linarith only [hTaylor, hle]

end PaperP1.FinitePolymerRemainder
