module

public import PaperP1.Combinatorics.SubsetSums
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

/-! # Complete square and cube expansions, including repeated indices -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.SubsetPowerSums

open Finset

variable {ι R : Type*} [DecidableEq ι] [CommRing R]

def elementary (p : ι → R) (G : Finset ι) (r : ℕ) : R :=
  ∑ I ∈ G.powersetCard r, ∏ x ∈ I, p x

def pairPower (p : ι → R) (G : Finset ι) : R :=
  ∑ e ∈ G.powersetCard 2, (∏ x ∈ e, p x) * ∑ x ∈ e, p x

omit [DecidableEq ι] in
theorem elementary_zero (p : ι → R) (G : Finset ι) : elementary p G 0 = 1 := by
  simp [elementary]

omit [DecidableEq ι] in
theorem elementary_one (p : ι → R) (G : Finset ι) : elementary p G 1 = ∑ x ∈ G, p x := by
  rw [elementary, SubsetSums.one]
  simp only [prod_singleton]

theorem elementary_insert (p : ι → R) (G : Finset ι) (x : ι) (hx : x ∉ G) (r : ℕ) :
    elementary p (insert x G) (r + 1) = elementary p G (r + 1) + p x * elementary p G r := by
  rw [elementary, SubsetSums.succ_insert G x hx r]
  change _ + _ = _ + p x * ∑ I ∈ G.powersetCard r, ∏ y ∈ I, p y
  rw [mul_sum]
  congr 1
  apply sum_congr rfl
  intro I hI
  exact prod_insert (fun hi ↦ hx ((mem_powersetCard.mp hI).1 hi))

theorem pairPower_insert (p : ι → R) (G : Finset ι) (x : ι) (hx : x ∉ G) :
    pairPower p (insert x G) = pairPower p G +
      (p x) ^ 2 * (∑ y ∈ G, p y) + p x * ∑ y ∈ G, (p y) ^ 2 := by
  rw [pairPower, SubsetSums.succ_insert G x hx 1, SubsetSums.one]
  have hsum : (∑ y ∈ G, (∏ z ∈ insert x {y}, p z) * ∑ z ∈ insert x {y}, p z) =
      (p x) ^ 2 * (∑ y ∈ G, p y) + p x * ∑ y ∈ G, (p y) ^ 2 := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro y hy
    have hxy : x ≠ y := fun h ↦ hx (h.symm ▸ hy)
    rw [prod_pair hxy, sum_pair hxy]
    ring
  rw [hsum]
  exact (add_assoc _ _ _).symm

theorem square (p : ι → R) (G : Finset ι) :
    (∑ x ∈ G, p x) ^ 2 = 2 * elementary p G 2 + ∑ x ∈ G, (p x) ^ 2 := by
  induction G using Finset.induction_on with
  | empty => simp [elementary, powersetCard_eq_empty.mpr (by norm_num : (∅ : Finset ι).card < 2)]
  | @insert x G hx ih =>
    rw [sum_insert hx, elementary_insert p G x hx 1, elementary_one, sum_insert hx]
    calc
      (p x + ∑ y ∈ G, p y) ^ 2 = (p x) ^ 2 + 2 * p x * (∑ y ∈ G, p y) + (∑ y ∈ G, p y) ^ 2 := by ring
      _ = _ := by rw [ih]; ring

theorem cube (p : ι → R) (G : Finset ι) :
    (∑ x ∈ G, p x) ^ 3 = 6 * elementary p G 3 + 3 * pairPower p G + ∑ x ∈ G, (p x) ^ 3 := by
  induction G using Finset.induction_on with
  | empty =>
    simp [elementary, pairPower,
      powersetCard_eq_empty.mpr (by norm_num : (∅ : Finset ι).card < 2),
      powersetCard_eq_empty.mpr (by norm_num : (∅ : Finset ι).card < 3)]
  | @insert x G hx ih =>
    rw [sum_insert hx, elementary_insert p G x hx 2, pairPower_insert p G x hx, sum_insert hx]
    calc
      (p x + ∑ y ∈ G, p y) ^ 3 = (p x) ^ 3 + 3 * (p x) ^ 2 * (∑ y ∈ G, p y) +
          3 * p x * (∑ y ∈ G, p y) ^ 2 + (∑ y ∈ G, p y) ^ 3 := by ring
      _ = _ := by rw [square, ih]; ring

end PaperP1.SubsetPowerSums
