module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import PaperP1.Algebra.FormalWordPolynomials
public import PaperP1.Algebra.ScaledSplitWordSquares

/-! # An actual nonzero integer certificate excludes characteristic two and every reduction collision -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BranchShiftReductionCertificate

open Finset
open scoped Classical

def differenceProduct (S : Finset ℤ) : ℤ := ∏ a ∈ S, ∏ b ∈ S.erase a, (a - b)

theorem difference_nonzero (S : Finset ℤ) : differenceProduct S ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro a _
  apply prod_ne_zero_iff.mpr
  intro b hb
  exact sub_ne_zero.mpr (Ne.symm (mem_erase.mp hb).1)

theorem difference_divides_of_collision (S : Finset ℤ) (p : ℕ) (a b : ℤ)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (he : (a : ZMod p) = (b : ZMod p)) :
    (p : ℤ) ∣ differenceProduct S := by
  have hz : ((a - b : ℤ) : ZMod p) = 0 := by rw [Int.cast_sub, he, sub_self]
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - b) p).mp hz
  have hin : a - b ∣ ∏ t ∈ S.erase a, (a - t) := dvd_prod_of_mem _ (mem_erase.mpr ⟨hab.symm, hb⟩)
  have hout : (∏ t ∈ S.erase a, (a - t)) ∣ differenceProduct S := dvd_prod_of_mem _ ha
  exact hd.trans (hin.trans hout)

theorem difference_injective_reduction (S : Finset ℤ) (p : ℕ) (hnot : ¬ (p : ℤ) ∣ differenceProduct S) :
    Set.InjOn (Int.cast : ℤ → ZMod p) (S : Set ℤ) := by
  intro a ha b hb he
  by_contra hab
  exact hnot (difference_divides_of_collision S p a b ha hb hab he)

theorem difference_abs_bound (S : Finset ℤ) (H : ℕ) (hH : ∀ a ∈ S, |a| ≤ (H : ℤ)) :
    |differenceProduct S| ≤ (2 * (H : ℤ)) ^ (S.card * (S.card - 1)) := by
  have hab (a b : ℤ) (ha : a ∈ S) (hb : b ∈ S) : |a - b| ≤ 2 * (H : ℤ) := by
    have hh := abs_sub a b
    linarith [hH a ha, hH b hb]
  unfold differenceProduct
  rw [abs_prod]
  calc
    _ ≤ ∏ a ∈ S, (2 * (H : ℤ)) ^ (S.card - 1) := by
      apply prod_le_prod₀ (fun _ _ ↦ abs_nonneg _)
      intro a ha
      rw [abs_prod]
      calc
        _ ≤ ∏ _b ∈ S.erase a, (2 * (H : ℤ)) := by
          apply prod_le_prod₀ (fun _ _ ↦ abs_nonneg _)
          intro b hb
          exact hab a b ha (mem_of_mem_erase hb)
        _ = _ := by rw [prod_const, card_erase_of_mem ha]
    _ = _ := by rw [prod_const, ← pow_mul, Nat.mul_comm]

def certificate (S : Finset ℤ) : ℤ := 2 * differenceProduct S

theorem nonzero (S : Finset ℤ) : certificate S ≠ 0 :=
  mul_ne_zero (by norm_num) (difference_nonzero S)

theorem divides_of_collision (S : Finset ℤ) (p : ℕ) (a b : ℤ)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (he : (a : ZMod p) = (b : ZMod p)) :
    (p : ℤ) ∣ certificate S :=
  (difference_divides_of_collision S p a b ha hb hab he).trans (dvd_mul_left _ _)

theorem injective_reduction (S : Finset ℤ) (p : ℕ) (hnot : ¬ (p : ℤ) ∣ certificate S) :
    Set.InjOn (Int.cast : ℤ → ZMod p) (S : Set ℤ) := by
  intro a ha b hb he
  by_contra hab
  exact hnot (divides_of_collision S p a b ha hb hab he)

theorem prime_ne_two (S : Finset ℤ) (p : ℕ) (hnot : ¬ (p : ℤ) ∣ certificate S) : p ≠ 2 := by
  intro hp
  subst p
  exact hnot ⟨differenceProduct S, rfl⟩

theorem natAbs_bound (S : Finset ℤ) (H : ℕ) (hH : ∀ a ∈ S, |a| ≤ (H : ℤ)) :
    (certificate S).natAbs ≤ 2 * (2 * H) ^ (S.card * (S.card - 1)) := by
  have hb : |certificate S| ≤ 2 * (2 * (H : ℤ)) ^ (S.card * (S.card - 1)) := by
    rw [certificate, abs_mul]
    rw [abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left (difference_abs_bound S H hH) (by norm_num)
  rw [Int.abs_eq_natAbs] at hb
  exact_mod_cast hb

theorem separable_on_subset (S T : Finset ℤ) (hTS : T ⊆ S) (p : ℕ) [Fact p.Prime]
    (hnot : ¬ (p : ℤ) ∣ certificate S) :
    (FormalWordPolynomials.linearOver (ZMod p) T).Separable := by
  have hinj := injective_reduction S p hnot
  have he : FormalWordPolynomials.linearOver (ZMod p) T =
      ∏ a ∈ T, (Polynomial.X - Polynomial.C (-((a : ℤ) : ZMod p))) := by
    simp only [FormalWordPolynomials.linearOver, map_neg, sub_neg_eq_add]
  rw [he, Polynomial.separable_prod_X_sub_C_iff']
  intro a ha b hb hab
  exact hinj (hTS ha) (hTS hb) (neg_injective hab)

theorem nonsquare_on_subset (S T : Finset ℤ) (hTS : T ⊆ S) (hne : T.Nonempty)
    (p : ℕ) [Fact p.Prime] (hnot : ¬ (p : ℤ) ∣ certificate S) :
    ¬ IsSquare (FormalWordPolynomials.linearOver (ZMod p) T) := by
  apply BivariateWordSquares.separable_not_square _ (separable_on_subset S T hTS p hnot)
  intro hu
  have hz := Polynomial.natDegree_eq_zero_of_isUnit hu
  rw [ScaledSplitWordSquares.linear_degree] at hz
  have := hne.card_pos
  omega

end PaperP1.BranchShiftReductionCertificate
