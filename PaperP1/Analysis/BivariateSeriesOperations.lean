module

public import PaperP1.Analysis.BivariateSeriesValue

/-! # Finite sums and literal monomial shifts of convergent bivariate real values -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateSeriesOperations

open Finset PaperP1.BiquadraticFormalNumerator PaperP1.BivariateSeriesValue

theorem absolutelySummable_add (f g : Series) (ξ η : ℝ)
    (hf : AbsolutelySummable f ξ η) (hg : AbsolutelySummable g ξ η) :
    AbsolutelySummable (f + g) ξ η :=
  (hf.add hg).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ by rw [diagonal_add]; exact norm_add_le _ _)

theorem absolutelySummable_scalar (c : ℚ) (f : Series) (ξ η : ℝ) (hf : AbsolutelySummable f ξ η) :
    AbsolutelySummable (PowerSeries.C (PowerSeries.C c) * f) ξ η := by
  unfold AbsolutelySummable
  simp only [diagonal_scalar, norm_mul]
  exact hf.mul_left ‖(c : ℝ)‖

theorem term_sum {ι : Type*} (S : Finset ι) (f : ι → Series) (ξ η : ℝ) (a b : ℕ) :
    term (∑ i ∈ S, f i) ξ η a b = ∑ i ∈ S, term (f i) ξ η a b := by
  simp only [term, coefficient_sum]
  push_cast
  rw [sum_mul, sum_mul]

theorem diagonal_sum {ι : Type*} (S : Finset ι) (f : ι → Series) (ξ η : ℝ) (n : ℕ) :
    diagonal (∑ i ∈ S, f i) ξ η n = ∑ i ∈ S, diagonal (f i) ξ η n := by
  simp only [diagonal, term_sum]
  exact sum_comm

theorem absolutelySummable_sum {ι : Type*} (S : Finset ι) (f : ι → Series) (ξ η : ℝ)
    (hf : ∀ i ∈ S, AbsolutelySummable (f i) ξ η) : AbsolutelySummable (∑ i ∈ S, f i) ξ η := by
  classical
  revert hf
  induction S using Finset.induction_on with
  | empty =>
    intro _
    simp [AbsolutelySummable, diagonal, term, coefficient]
  | @insert i S hi ih =>
    intro h
    rw [sum_insert hi]
    exact absolutelySummable_add _ _ ξ η (h i (mem_insert_self i S)) (ih (fun j hj ↦ h j (mem_insert_of_mem hj)))

theorem value_sum {ι : Type*} (S : Finset ι) (f : ι → Series) (ξ η : ℝ)
    (hf : ∀ i ∈ S, AbsolutelySummable (f i) ξ η) :
    value (∑ i ∈ S, f i) ξ η = ∑ i ∈ S, value (f i) ξ η := by
  unfold value
  simp only [diagonal_sum]
  exact Summable.tsum_finsetSum (fun i hi ↦ (hf i hi).of_norm)

theorem term_shift (f : Series) (sx sy : ℕ) (ξ η : ℝ) (a b : ℕ) :
    term (shift sx sy f) ξ η a b =
      if sx ≤ a ∧ sy ≤ b then ξ ^ sx * η ^ sy * term f ξ η (a - sx) (b - sy) else 0 := by
  by_cases h : sx ≤ a ∧ sy ≤ b
  · have hx : ξ ^ a = ξ ^ sx * ξ ^ (a - sx) := by rw [← pow_add]; congr 1; omega
    have hy : η ^ b = η ^ sy * η ^ (b - sy) := by rw [← pow_add]; congr 1; omega
    simp only [term, coefficient_shift, ite_eq_left h]
    rw [hx, hy]
    ring
  · simp only [term, coefficient_shift, ite_eq_right h, Rat.cast_zero, zero_mul]

theorem diagonal_shift (f : Series) (sx sy : ℕ) (ξ η : ℝ) (n : ℕ) :
    diagonal (shift sx sy f) ξ η n =
      if sx + sy ≤ n then ξ ^ sx * η ^ sy * diagonal f ξ η (n - (sx + sy)) else 0 := by
  by_cases hn : sx + sy ≤ n
  · rw [ite_eq_left hn]
    have hfilter : diagonal (shift sx sy f) ξ η n =
        ∑ p ∈ (Finset.antidiagonal n).filter (fun p ↦ sx ≤ p.1 ∧ sy ≤ p.2),
          ξ ^ sx * η ^ sy * term f ξ η (p.1 - sx) (p.2 - sy) := by
      rw [diagonal, sum_filter]
      exact sum_congr rfl (fun p _ ↦ term_shift f sx sy ξ η p.1 p.2)
    rw [hfilter, diagonal, mul_sum]
    refine sum_bij (fun p _ ↦ (p.1 - sx, p.2 - sy)) ?_ ?_ ?_ ?_
    · intro p hp
      have h := mem_filter.mp hp
      have he := Finset.mem_antidiagonal.mp h.1
      apply Finset.mem_antidiagonal.mpr
      omega
    · intro p hp q hq he
      have hp' := (mem_filter.mp hp).2
      have hq' := (mem_filter.mp hq).2
      have hx := congrArg Prod.fst he
      have hy := congrArg Prod.snd he
      apply Prod.ext <;> dsimp at hx hy ⊢ <;> omega
    · intro q hq
      have he := Finset.mem_antidiagonal.mp hq
      refine ⟨(q.1 + sx, q.2 + sy), ?_, ?_⟩
      · apply mem_filter.mpr
        constructor
        · apply Finset.mem_antidiagonal.mpr
          omega
        · exact ⟨by omega, by omega⟩
      · apply Prod.ext <;> dsimp <;> omega
    · intro p _
      rfl
  · rw [ite_eq_right hn]
    apply sum_eq_zero
    intro p hp
    have he := Finset.mem_antidiagonal.mp hp
    have hnot : ¬ (sx ≤ p.1 ∧ sy ≤ p.2) := by omega
    rw [term_shift, ite_eq_right hnot]

theorem absolutelySummable_shift (f : Series) (sx sy : ℕ) (ξ η : ℝ) (hf : AbsolutelySummable f ξ η) :
    AbsolutelySummable (shift sx sy f) ξ η := by
  unfold AbsolutelySummable
  apply (summable_nat_add_iff (sx + sy)).mp
  have he : (fun n : ℕ ↦ ‖diagonal (shift sx sy f) ξ η (n + (sx + sy))‖) =
      (fun n : ℕ ↦ ‖ξ ^ sx * η ^ sy‖ * ‖diagonal f ξ η n‖) := by
    funext n
    rw [diagonal_shift, ite_eq_left (by omega), Nat.add_sub_cancel_right, norm_mul]
  rw [he]
  exact hf.mul_left ‖ξ ^ sx * η ^ sy‖

theorem value_shift (f : Series) (sx sy : ℕ) (ξ η : ℝ) (hf : AbsolutelySummable f ξ η) :
    value (shift sx sy f) ξ η = ξ ^ sx * η ^ sy * value f ξ η := by
  have hshift := absolutelySummable_shift f sx sy ξ η hf
  have hzero : ∑ n ∈ range (sx + sy), diagonal (shift sx sy f) ξ η n = 0 := by
    apply sum_eq_zero
    intro n hn
    rw [diagonal_shift, ite_eq_right (by have h := mem_range.mp hn; omega)]
  have hsplit := Summable.sum_add_tsum_nat_add (sx + sy) hshift.of_norm
  rw [hzero, zero_add] at hsplit
  unfold value
  rw [← hsplit]
  calc
    _ = ∑' n : ℕ, ξ ^ sx * η ^ sy * diagonal f ξ η n := by
      apply tsum_congr
      intro n
      rw [diagonal_shift, ite_eq_left (by omega), Nat.add_sub_cancel_right]
    _ = _ := tsum_mul_left

end PaperP1.BivariateSeriesOperations
