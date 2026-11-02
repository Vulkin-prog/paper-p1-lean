module

public import PaperP1.Combinatorics.FinitePolymerBound
public import PaperP1.Analysis.BanachFactorialRemainder

/-! # A quadratic finite polymer tail from actual union-recoverable decompositions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FinitePolymerTail

open Finset

variable {ι : Type*} [DecidableEq ι]

def tail (A : Finset ι) : Finset (Finset ι) := A.powerset.filter (fun P ↦ 2 ≤ P.card)

theorem tail_eq (w : ι → ℝ) (A : Finset ι) :
    (∑ P ∈ tail A, ∏ x ∈ P, w x) = (∏ x ∈ A, (1 + w x)) - 1 - ∑ x ∈ A, w x := by
  classical
  have hlow : A.powerset.filter (fun P ↦ ¬2 ≤ P.card) = insert ∅ (A.image singleton) := by
    ext P
    constructor
    · intro hP
      obtain ⟨hPA, hc⟩ := mem_filter.mp hP
      have hsub := mem_powerset.mp hPA
      by_cases hz : P.card = 0
      · exact mem_insert.mpr (Or.inl (card_eq_zero.mp hz))
      · have hone : P.card = 1 := by omega
        obtain ⟨x, rfl⟩ := card_eq_one.mp hone
        exact mem_insert.mpr (Or.inr (mem_image.mpr ⟨x, hsub (mem_singleton_self _), rfl⟩))
    · intro hP
      rcases mem_insert.mp hP with rfl | hP
      · simp
      · obtain ⟨x, hx, rfl⟩ := mem_image.mp hP
        exact mem_filter.mpr ⟨mem_powerset.mpr (singleton_subset_iff.mpr hx), by simp⟩
  have hlow_sum : (∑ P ∈ A.powerset.filter (fun P ↦ ¬2 ≤ P.card), ∏ x ∈ P, w x) =
      1 + ∑ x ∈ A, w x := by
    rw [hlow, sum_insert (by simp)]
    rw [sum_image (fun x _ y _ h ↦ by simpa only [singleton_inj] using h)]
    simp only [prod_empty, prod_singleton]
  have hsplit := sum_filter_add_sum_filter_not A.powerset (fun P ↦ 2 ≤ P.card)
    (fun P ↦ ∏ x ∈ P, w x)
  rw [hlow_sum, ← prod_one_add A] at hsplit
  change (∑ P ∈ tail A, ∏ x ∈ P, w x) + (1 + ∑ x ∈ A, w x) = _ at hsplit
  linarith only [hsplit]

theorem tail_bound (w : ι → ℝ) (hw : ∀ x, 0 ≤ w x) (A : Finset ι) :
    (∑ P ∈ tail A, ∏ x ∈ P, w x) ≤
      ((∑ x ∈ A, w x) ^ 2 / 2) * Real.exp (∑ x ∈ A, w x) := by
  let W := ∑ x ∈ A, w x
  have hW : 0 ≤ W := sum_nonneg fun x _ ↦ hw x
  have hprod := Real.prod_one_add_le_exp_sum A hw
  have hTaylor := BanachFactorialRemainder.norm_exp_sub_partial_le (W : ℝ) 2
  have hpart : (∑ j ∈ range 2, ((j.factorial : ℝ)⁻¹) • W ^ j) = 1 + W := by
    norm_num [sum_range_succ]
  rw [hpart, ← Real.exp_eq_exp_ℝ] at hTaylor
  simp only [Real.norm_eq_abs, abs_of_nonneg hW] at hTaylor
  norm_num only [Nat.factorial, Nat.cast_one, Nat.cast_ofNat, mul_one] at hTaylor
  calc
    _ = (∏ x ∈ A, (1 + w x)) - 1 - W := tail_eq w A
    _ ≤ Real.exp W - 1 - W := by linarith only [hprod]
    _ ≤ |Real.exp W - (1 + W)| := by
      convert le_abs_self (Real.exp W - (1 + W)) using 1; ring
    _ ≤ _ := hTaylor

theorem covered_bound {V : Type*} [DecidableEq V] (F : Finset (Finset V))
    (A : Finset (Finset V)) (v : Finset V → ℝ) (w : Finset V → ℝ)
    (hw : ∀ C, 0 ≤ w C)
    (hcover : ∀ D ∈ F, ∃ P ⊆ A, P.biUnion id = D ∧ 2 ≤ P.card ∧ v D ≤ ∏ C ∈ P, w C) :
    (∑ D ∈ F, v D) ≤ ((∑ C ∈ A, w C) ^ 2 / 2) * Real.exp (∑ C ∈ A, w C) := by
  classical
  let select (D : Finset V) : Finset (Finset V) :=
    if h : D ∈ F then Classical.choose (hcover D h) else ∅
  have hs (D : Finset V) (hD : D ∈ F) : select D ⊆ A ∧ (select D).biUnion id = D ∧
      2 ≤ (select D).card ∧ v D ≤ ∏ C ∈ select D, w C := by
    dsimp [select]
    rw [dite_eq_left hD]
    exact Classical.choose_spec (hcover D hD)
  have hinj : Set.InjOn select (↑F : Set (Finset V)) := by
    intro D hD E hE h
    have hu := congrArg (fun P : Finset (Finset V) ↦ P.biUnion id) h
    rwa [(hs D hD).2.1, (hs E hE).2.1] at hu
  have hsub : F.image select ⊆ tail A := by
    intro P hP
    obtain ⟨D, hD, rfl⟩ := mem_image.mp hP
    exact mem_filter.mpr ⟨mem_powerset.mpr (hs D hD).1, (hs D hD).2.2.1⟩
  calc
    _ ≤ ∑ D ∈ F, ∏ C ∈ select D, w C := sum_le_sum fun D hD ↦ (hs D hD).2.2.2
    _ = ∑ P ∈ F.image select, ∏ C ∈ P, w C :=
      (sum_image (f := fun P : Finset (Finset V) ↦ ∏ C ∈ P, w C) hinj).symm
    _ ≤ ∑ P ∈ tail A, ∏ C ∈ P, w C := sum_le_sum_of_subset_of_nonneg hsub
      (fun P _ _ ↦ prod_nonneg fun C _ ↦ hw C)
    _ ≤ _ := tail_bound w hw A

end PaperP1.FinitePolymerTail
