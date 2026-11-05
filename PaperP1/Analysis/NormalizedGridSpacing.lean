module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! # Actual grid spacing and removal of at most two endpoint points

After removing its actual smallest and largest members, any finite population
on the normalized grid has a full grid-step margin from both selected endpoints.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedGridSpacing

open Finset


theorem integer_gap (N : ℕ) (hN : 0 < N) (m n : ℤ) (hmn : m < n) :
    1 / (N : ℝ) ≤ (n : ℝ) / N - (m : ℝ) / N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : (m : ℝ) + 1 ≤ n := by exact_mod_cast (Int.add_one_le_iff.mpr hmn)
  rw [← sub_div]
  exact div_le_div_of_nonneg_right (by linarith only [hh]) hNR.le

theorem separation (N : ℕ) (hN : 0 < N) (x y : ℝ)
    (hx : ∃ m : ℤ, x = (m : ℝ) / N) (hy : ∃ n : ℤ, y = (n : ℝ) / N) (hxy : x < y) :
    1 / (N : ℝ) ≤ y - x := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hy
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hmnR : (m : ℝ) < n := (div_lt_div_iff_of_pos_right hNR).mp hxy
  exact integer_gap N hN m n (by exact_mod_cast hmnR)

theorem trimmed_population (N : ℕ) (hN : 0 < N) (T : Finset ℝ) (hT : T.Nonempty)
    (hgrid : ∀ t ∈ T, ∃ m : ℤ, t = (m : ℝ) / N) :
    ∃ a ∈ T, ∃ b ∈ T, ∃ R : Finset ℝ,
      R ⊆ T ∧ T.card ≤ R.card + 2 ∧
      (∀ t ∈ T, a ≤ t ∧ t ≤ b) ∧
      ∀ t ∈ R, a + 1 / (N : ℝ) ≤ t ∧ t ≤ b - 1 / (N : ℝ) := by
  classical
  let a := T.min' hT
  let b := T.max' hT
  have ha : a ∈ T := T.min'_mem hT
  have hb : b ∈ T := T.max'_mem hT
  let R := (T.erase a).erase b
  have hsub : R ⊆ T := fun t ht ↦ (mem_erase.mp (mem_erase.mp ht).2).2
  refine ⟨a, ha, b, hb, R, hsub, ?_, ?_, ?_⟩
  · have hca := card_erase_add_one ha
    by_cases hba : b ∈ T.erase a
    · have hcb := card_erase_add_one hba
      change T.card ≤ ((T.erase a).erase b).card + 2
      omega
    · change T.card ≤ ((T.erase a).erase b).card + 2
      rw [erase_eq_of_notMem hba]
      omega
  · exact fun t ht ↦ ⟨T.min'_le t ht, T.le_max' t ht⟩
  · intro t ht
    have htT := hsub ht
    have hta : t ≠ a := (mem_erase.mp (mem_erase.mp ht).2).1
    have htb : t ≠ b := (mem_erase.mp ht).1
    have hat : a < t := lt_of_le_of_ne (T.min'_le t htT) hta.symm
    have hbt : t < b := lt_of_le_of_ne (T.le_max' t htT) htb
    have hleft := separation N hN a t (hgrid a ha) (hgrid t htT) hat
    have hright := separation N hN t b (hgrid t htT) (hgrid b hb) hbt
    exact ⟨by linarith only [hleft], by linarith only [hright]⟩

end PaperP1.NormalizedGridSpacing
