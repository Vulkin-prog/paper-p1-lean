module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.Positivity
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! # The finite weight budget in the short-product exposure argument -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExposureWeights

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def degree (H : Finset (Finset ι)) (w : Finset ι → ℝ) (i : ι) : ℝ :=
  ∑ S ∈ H.filter (fun S ↦ i ∈ S), w S

def correction (H : Finset (Finset ι)) (w : Finset ι → ℝ) (last : ι) : ℝ :=
  ∑ S ∈ H, (1 - (S.card : ℝ) / 2 + if last ∈ S then 1 / 2 else 0) * w S

theorem total_degree (H : Finset (Finset ι)) (w : Finset ι → ℝ) :
    (∑ i, degree H w i) = ∑ S ∈ H, (S.card : ℝ) * w S := by
  unfold degree
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro S _
  rw [← sum_filter]
  simp

omit [Fintype ι] in
theorem correction_identity (H : Finset (Finset ι)) (w : Finset ι → ℝ) (last : ι) :
    correction H w last = (∑ S ∈ H, (1 - (S.card : ℝ) / 2) * w S) + degree H w last / 2 := by
  unfold correction degree
  rw [sum_filter, sum_div]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro S _
  split_ifs <;> ring

omit [Fintype ι] in
theorem correction_le_half_degree (H : Finset (Finset ι)) (w : Finset ι → ℝ)
    (hw : ∀ S ∈ H, 0 ≤ w S) (hH : ∀ S ∈ H, 2 ≤ S.card) (last : ι) :
    correction H w last ≤ degree H w last / 2 := by
  rw [correction_identity]
  have hsum : (∑ S ∈ H, (1 - (S.card : ℝ) / 2) * w S) ≤ 0 := by
    apply sum_nonpos
    intro S hS
    have hc : (2 : ℝ) ≤ S.card := by exact_mod_cast hH S hS
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hw S hS)
  linarith

theorem correction_as_totals (H : Finset (Finset ι)) (w : Finset ι → ℝ) (last : ι) :
    correction H w last = (∑ S ∈ H, w S) - (∑ i, degree H w i) / 2 + degree H w last / 2 := by
  rw [correction_identity, total_degree]
  have heq : (∑ S ∈ H, (1 - (S.card : ℝ) / 2) * w S) =
      (∑ S ∈ H, w S) - (∑ S ∈ H, (S.card : ℝ) * w S) / 2 := by
    simp_rw [sub_mul, one_mul, div_mul_eq_mul_div]
    rw [sum_sub_distrib, sum_div]
  rw [heq]

theorem exists_small_last [Nonempty ι] (H : Finset (Finset ι)) (w : Finset ι → ℝ)
    (hw : ∀ S ∈ H, 0 ≤ w S) (hH : ∀ S ∈ H, 2 ≤ S.card) :
    ∃ last : ι, correction H w last ≤
      (∑ S ∈ H, (S.card : ℝ) * w S) / (2 * Fintype.card ι) := by
  obtain ⟨i, _, hmin⟩ := (univ : Finset ι).exists_min_image (degree H w) univ_nonempty
  have hv : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hm : degree H w i * Fintype.card ι ≤ ∑ j, degree H w j := by
    calc
      _ = ∑ _j : ι, degree H w i := by simp [mul_comm]
      _ ≤ _ := sum_le_sum fun j hj ↦ hmin j hj
  have hd := (le_div_iff₀ hv).mpr hm
  rw [total_degree] at hd
  refine ⟨i, (correction_le_half_degree H w hw hH i).trans ?_⟩
  have hhalf := div_le_div_of_nonneg_right hd (by norm_num : (0 : ℝ) ≤ 2)
  convert hhalf using 1; ring

theorem exists_last_exponent_le [Nonempty ι] (H : Finset (Finset ι)) (w : Finset ι → ℝ)
    (hw : ∀ S ∈ H, 0 ≤ w S) (hH : ∀ S ∈ H, 2 ≤ S.card)
    (d E : ℝ) (hd : 0 < d)
    (hbudget : (∑ S ∈ H, (S.card : ℝ) * w S) ≤ Fintype.card ι * d + E) :
    ∃ last : ι, ((Fintype.card ι : ℝ) - 1) / 2 + correction H w last / d ≤
      Fintype.card ι / 2 + E / (2 * d * Fintype.card ι) := by
  obtain ⟨last, hlast⟩ := exists_small_last H w hw hH
  have hv : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hb := div_le_div_of_nonneg_right hbudget (by positivity : (0 : ℝ) ≤ 2 * Fintype.card ι)
  have hc := div_le_div_of_nonneg_right (hlast.trans hb) hd.le
  refine ⟨last, ?_⟩
  have heq : ((Fintype.card ι * d + E) / (2 * Fintype.card ι)) / d =
      1 / 2 + E / (2 * d * Fintype.card ι) := by
    field_simp
  rw [heq] at hc
  linarith

end PaperP1.ExposureWeights
