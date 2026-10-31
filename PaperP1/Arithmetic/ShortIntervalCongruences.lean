module

public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Fintype.BigOperators
public import Lean.Elab.Tactic.Omega

/-! # At most one centre for coprime congruences on a short interval -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShortIntervalCongruences

open Finset

variable {ι : Type*} [Fintype ι]

def fibre (U N : ℕ) (G w : ι → ℕ) : Finset ℕ :=
  (Finset.Ico U (U + N)).filter fun z ↦ ∀ i, G i ∣ z - 1 + w i

theorem mem_fibre (U N : ℕ) (G w : ι → ℕ) (z : ℕ) :
    z ∈ fibre U N G w ↔ z ∈ Finset.Ico U (U + N) ∧ ∀ i, G i ∣ z - 1 + w i :=
  mem_filter

omit [Fintype ι] in
theorem common_divisors_modEq (G w : ι → ℕ) (z z' : ℕ) (hz : 1 ≤ z) (hz' : 1 ≤ z')
    (hdiv : ∀ i, G i ∣ z - 1 + w i) (hdiv' : ∀ i, G i ∣ z' - 1 + w i) :
    ∀ i, Nat.ModEq (G i) z z' := by
  intro i
  have h := (hdiv i).modEq_zero_nat.trans (hdiv' i).zero_modEq_nat
  have hcancel := h.add_right_cancel' (w i)
  have hadd := hcancel.add_right 1
  simpa only [Nat.sub_add_cancel hz, Nat.sub_add_cancel hz'] using hadd

theorem product_dvd_difference (G : ι → ℕ)
    (hcop : Pairwise (fun i j ↦ Nat.Coprime (G i) (G j))) (z z' : ℕ)
    (hmod : ∀ i, Nat.ModEq (G i) z z') : (∏ i, G i) ∣ z' - z := by
  have hpair : (↑(univ : Finset ι) : Set ι).Pairwise (fun i j ↦ Nat.Coprime (G i) (G j)) := by
    intro i _ j _ hij
    exact hcop hij
  have heq := Finset.lcm_eq_prod hpair
  change (univ.prod G) ∣ z' - z
  rw [← heq]
  exact Finset.lcm_dvd (fun i _ ↦ (hmod i).dvd')

/-- The product need only be at least the interval length. -/
theorem eq_of_common_divisors (U N : ℕ) (G w : ι → ℕ) (hU : 1 ≤ U)
    (hcop : Pairwise (fun i j ↦ Nat.Coprime (G i) (G j))) (hprod : N ≤ ∏ i, G i)
    (z z' : ℕ) (hz : z ∈ Finset.Ico U (U + N)) (hz' : z' ∈ Finset.Ico U (U + N))
    (hdiv : ∀ i, G i ∣ z - 1 + w i) (hdiv' : ∀ i, G i ∣ z' - 1 + w i) : z = z' := by
  obtain ⟨hzlo, hzhi⟩ := mem_Ico.mp hz
  obtain ⟨hz'lo, hz'hi⟩ := mem_Ico.mp hz'
  have hmod := common_divisors_modEq G w z z' (by omega) (by omega) hdiv hdiv'
  have hdiff := product_dvd_difference G hcop z z' hmod
  have hdiff' := product_dvd_difference G hcop z' z (fun i ↦ (hmod i).symm)
  have hzero : z' - z = 0 := Nat.eq_zero_of_dvd_of_lt hdiff (lt_of_lt_of_le (by omega) hprod)
  have hzero' : z - z' = 0 := Nat.eq_zero_of_dvd_of_lt hdiff' (lt_of_lt_of_le (by omega) hprod)
  omega

theorem card_fibre_le_one (U N : ℕ) (G w : ι → ℕ) (hU : 1 ≤ U)
    (hcop : Pairwise (fun i j ↦ Nat.Coprime (G i) (G j))) (hprod : N ≤ ∏ i, G i) :
    (fibre U N G w).card ≤ 1 := by
  apply card_le_one.mpr
  intro z hz z' hz'
  obtain ⟨hz, hdiv⟩ := mem_filter.mp hz
  obtain ⟨hz', hdiv'⟩ := mem_filter.mp hz'
  exact eq_of_common_divisors U N G w hU hcop hprod z z' hz hz' hdiv hdiv'

end PaperP1.ShortIntervalCongruences
