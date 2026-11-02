module

public import PaperP1.Algebra.PolynomialHeightArithmetic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Data.Fintype.Perm

/-! # Explicit integer polynomial product and determinant heights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialDeterminantHeight

open Finset Polynomial PaperP1.PolynomialHeightArithmetic

theorem product_degree {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) (d : ℕ)
    (hf : ∀ i, (f i).natDegree ≤ d) : (∏ i ∈ s, f i).natDegree ≤ s.card * d := by
  calc
    _ ≤ ∑ i ∈ s, (f i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i ∈ s, d := sum_le_sum (fun i _ ↦ hf i)
    _ = _ := by simp

theorem product_height {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) (d H : ℕ)
    (hf : ∀ i, (f i).natDegree ≤ d) (hH : ∀ i, integerPolynomialHeight (f i) ≤ H) :
    integerPolynomialHeight (∏ i ∈ s, f i) ≤ (s.card * d + 1) ^ s.card * H ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [prod_empty, card_empty, zero_mul, zero_add, pow_zero, one_mul]
    apply integer_height_le
    intro n
    change ((1 : ℤ[X]).coeff n).natAbs ≤ 1
    rw [Polynomial.coeff_one]
    split_ifs <;> norm_num
  | @insert a s ha ih =>
    rw [prod_insert ha, card_insert_of_notMem ha]
    let C₀ := (s.card + 1) * d + 1
    have hcost : (f a).natDegree + (∏ i ∈ s, f i).natDegree + 1 ≤ C₀ := by
      calc
        _ ≤ d + s.card * d + 1 := Nat.add_le_add_right (Nat.add_le_add (hf a) (product_degree s f d hf)) 1
        _ = _ := by dsimp [C₀]; ring
    have hsmall : s.card * d + 1 ≤ C₀ := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_right d (Nat.le_succ s.card)) 1
    calc
      _ ≤ ((f a).natDegree + (∏ i ∈ s, f i).natDegree + 1) *
          integerPolynomialHeight (f a) * integerPolynomialHeight (∏ i ∈ s, f i) := integer_height_mul _ _
      _ ≤ C₀ * H * ((s.card * d + 1) ^ s.card * H ^ s.card) :=
        Nat.mul_le_mul (Nat.mul_le_mul hcost (hH a)) ih
      _ ≤ C₀ * H * (C₀ ^ s.card * H ^ s.card) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hsmall _))
      _ = _ := by change C₀ * H * (C₀ ^ s.card * H ^ s.card) = C₀ ^ (s.card + 1) * H ^ (s.card + 1); rw [pow_succ, pow_succ]; ring

theorem unit_mul_height (u : ℤˣ) (p : ℤ[X]) :
    integerPolynomialHeight ((u : ℤ) * p) ≤ integerPolynomialHeight p := by
  have hcast : C (u : ℤ) = ((u : ℤ) : ℤ[X]) := by
    simpa only [Int.cast_id] using (C_eq_intCast (R := ℤ) (u : ℤ))
  have h := integer_height_C_mul (u : ℤ) p
  rwa [hcast, Int.units_natAbs, one_mul] at h

theorem determinant_height {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ[X]) (d H : ℕ)
    (hdeg : ∀ i j, (M i j).natDegree ≤ d) (hheight : ∀ i j, integerPolynomialHeight (M i j) ≤ H) :
    integerPolynomialHeight M.det ≤ (Fintype.card ι).factorial *
      (((Fintype.card ι * d + 1) * H) ^ Fintype.card ι) := by
  classical
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, integerPolynomialHeight
        (((Equiv.Perm.sign σ : ℤ) : ℤ[X]) * ∏ i, M (σ i) i) := integer_height_sum _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, ((Fintype.card ι * d + 1) ^ Fintype.card ι * H ^ Fintype.card ι) := by
      apply sum_le_sum
      intro σ _
      exact (unit_mul_height (Equiv.Perm.sign σ) _).trans (by
        simpa only [card_univ] using product_height univ (fun i ↦ M (σ i) i) d H
          (fun i ↦ hdeg (σ i) i) (fun i ↦ hheight (σ i) i))
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul, Fintype.card_perm, mul_pow, Nat.cast_id]

end PaperP1.PolynomialDeterminantHeight
