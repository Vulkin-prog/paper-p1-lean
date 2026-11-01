module

public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-! # A finite product bound in terms of its lcm and pairwise gcd heights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GcdLcmProductBound

open Finset

theorem gcd_prod_dvd {ι : Type*} (S : Finset ι) (f : ι → ℕ) (a : ℕ) :
    Nat.gcd a (S.prod f) ∣ S.prod (fun i ↦ Nat.gcd a (f i)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [prod_insert hi, prod_insert hi]
    exact (gcd_mul_dvd_mul_gcd a (f i) (S.prod f)).trans (Nat.mul_dvd_mul_left _ ih)

theorem gcd_lcm_le {ι : Type*} (S : Finset ι) (f : ι → ℕ) (a B : ℕ)
    (ha : 0 < a)
    (hbound : ∀ i ∈ S, Nat.gcd a (f i) ≤ B) :
    Nat.gcd a (S.lcm f) ≤ B ^ S.card := by
  have hdiv : Nat.gcd a (S.lcm f) ∣ S.prod (fun i ↦ Nat.gcd a (f i)) :=
    (gcd_dvd_gcd (dvd_refl a) (lcm_dvd_prod S f)).trans (gcd_prod_dvd S f a)
  have hpos : 0 < S.prod (fun i ↦ Nat.gcd a (f i)) :=
    prod_pos (fun i _ ↦ Nat.gcd_pos_of_pos_left _ ha)
  exact (Nat.le_of_dvd hpos hdiv).trans (by
    calc
      _ ≤ S.prod (fun _ ↦ B) := prod_le_prod hbound
      _ = _ := by simp)

theorem product_le_lcm_mul_bound {ι : Type*} (S : Finset ι) (f : ι → ℕ) (B : ℕ)
    (hB : 1 ≤ B) (hpos : ∀ i ∈ S, 0 < f i)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Nat.gcd (f i) (f j) ≤ B) :
    S.prod f ≤ S.lcm f * B ^ (S.card ^ 2) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hip : 0 < f i := hpos i (mem_insert_self i S)
    have hp : ∀ j ∈ S, 0 < f j := fun j hj ↦ hpos j (mem_insert_of_mem hj)
    have hpp : ∀ j ∈ S, ∀ k ∈ S, j ≠ k → Nat.gcd (f j) (f k) ≤ B :=
      fun j hj k hk hjk ↦ hpair j (mem_insert_of_mem hj) k (mem_insert_of_mem hk) hjk
    have hbound := ih hp hpp
    have hgcd : Nat.gcd (f i) (S.lcm f) ≤ B ^ S.card :=
      gcd_lcm_le S f (f i) B hip (fun j hj ↦
        hpair i (mem_insert_self i S) j (mem_insert_of_mem hj) (by intro heq; exact hi (heq ▸ hj)))
    rw [prod_insert hi, lcm_insert, card_insert_of_notMem hi, lcm_eq_nat_lcm]
    calc
      _ ≤ f i * (S.lcm f * B ^ (S.card ^ 2)) := Nat.mul_le_mul_left _ hbound
      _ = (Nat.gcd (f i) (S.lcm f) * Nat.lcm (f i) (S.lcm f)) * B ^ (S.card ^ 2) := by
        rw [Nat.gcd_mul_lcm]; ring
      _ ≤ (B ^ S.card * Nat.lcm (f i) (S.lcm f)) * B ^ (S.card ^ 2) := by gcongr
      _ = Nat.lcm (f i) (S.lcm f) * B ^ (S.card + S.card ^ 2) := by rw [pow_add]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB (by nlinarith : S.card + S.card ^ 2 ≤ (S.card + 1) ^ 2))

end PaperP1.GcdLcmProductBound
