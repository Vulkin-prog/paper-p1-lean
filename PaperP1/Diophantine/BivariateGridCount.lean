module

public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Algebra.Field.Rat
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-! # Coefficient-independent counts on actual bivariate polynomial grids -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateGridCount

open Finset MvPolynomial

variable {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]

def zeros (p : MvPolynomial (Fin 2) R) (S : Finset R) : Finset (Fin 2 → R) :=
  (Fintype.piFinset fun _ : Fin 2 ↦ S).filter fun f ↦ eval f p = 0

def level (p : MvPolynomial (Fin 2) R) (c : R) (S : Finset R) : Finset (Fin 2 → R) :=
  (Fintype.piFinset fun _ : Fin 2 ↦ S).filter fun f ↦ eval f p = c

theorem zero_grid_bound (p : MvPolynomial (Fin 2) R) (hp : p ≠ 0) (S : Finset R) :
    (zeros p S).card ≤ p.totalDegree * S.card := by
  obtain rfl | hS := S.eq_empty_or_nonempty
  · simp [zeros]
  · have hs : (0 : ℚ≥0) < S.card := by exact_mod_cast card_pos.mpr hS
    have h := MvPolynomial.schwartz_zippel_totalDegree hp S
    have hmul := (div_le_iff₀ (pow_pos hs 2)).mp h
    have heq : (p.totalDegree : ℚ≥0) / S.card * (S.card : ℚ≥0) ^ 2 =
        (p.totalDegree : ℚ≥0) * S.card := by
      field_simp
    rw [heq] at hmul
    exact_mod_cast hmul

omit [IsDomain R] [DecidableEq R] in
theorem sub_constant_ne_zero (p : MvPolynomial (Fin 2) R) (c : R)
    (hconstant : p.constantCoeff = 0) (hc : c ≠ 0) : p - C c ≠ 0 := by
  intro h
  have hcc := congrArg (constantCoeff : MvPolynomial (Fin 2) R → R) h
  simp only [map_sub, constantCoeff_C, map_zero, hconstant, zero_sub] at hcc
  exact hc (neg_eq_zero.mp hcc)

omit [IsDomain R] in
theorem level_eq_zeros (p : MvPolynomial (Fin 2) R) (c : R) (S : Finset R) :
    level p c S = zeros (p - C c) S := by
  ext f
  simp only [level, zeros, mem_filter, map_sub, eval_C, sub_eq_zero]

omit [IsDomain R] [DecidableEq R] in
theorem shifted_degree_le (p : MvPolynomial (Fin 2) R) (c : R) :
    (p - C c).totalDegree ≤ p.totalDegree := by
  have h := totalDegree_add p (C (-c))
  rw [totalDegree_C] at h
  simpa only [map_neg, sub_eq_add_neg, max_eq_left (Nat.zero_le _)] using h

theorem nonzero_level_grid_bound (p : MvPolynomial (Fin 2) R) (c : R)
    (hconstant : p.constantCoeff = 0) (hc : c ≠ 0) (S : Finset R) :
    (level p c S).card ≤ p.totalDegree * S.card := by
  rw [level_eq_zeros]
  exact (zero_grid_bound (p - C c) (sub_constant_ne_zero p c hconstant hc) S).trans
    (Nat.mul_le_mul_right S.card (shifted_degree_le p c))

theorem integer_box_bound (p : MvPolynomial (Fin 2) ℤ) (c : ℤ)
    (hconstant : p.constantCoeff = 0) (hc : c ≠ 0) (H : ℕ) :
    (level p c (Finset.Icc (-(H : ℤ)) H)).card ≤ p.totalDegree * (2 * H + 1) := by
  have hcard : (Finset.Icc (-(H : ℤ)) H).card = 2 * H + 1 := by rw [Int.card_Icc]; omega
  exact (nonzero_level_grid_bound p c hconstant hc _).trans_eq (congrArg (p.totalDegree * ·) hcard)

omit [IsDomain R] [DecidableEq R] in
theorem homogeneous_constant_zero (p : MvPolynomial (Fin 2) R) (d : ℕ)
    (hd : 0 < d) (hp : p.IsHomogeneous d) : p.constantCoeff = 0 := by
  rw [constantCoeff_eq]
  exact hp.coeff_eq_zero (by simpa using hd.ne)

theorem homogeneous_level_grid_bound (p : MvPolynomial (Fin 2) R) (d : ℕ)
    (hd : 0 < d) (hp : p.IsHomogeneous d) (c : R) (hc : c ≠ 0) (S : Finset R) :
    (level p c S).card ≤ p.totalDegree * S.card :=
  nonzero_level_grid_bound p c (homogeneous_constant_zero p d hd hp) hc S

theorem homogeneous_grid_degree_bound (p : MvPolynomial (Fin 2) R) (d : ℕ)
    (hd : 0 < d) (hp : p.IsHomogeneous d) (c : R) (hc : c ≠ 0) (S : Finset R) :
    (level p c S).card ≤ d * S.card :=
  (homogeneous_level_grid_bound p d hd hp c hc S).trans
    (Nat.mul_le_mul_right S.card hp.totalDegree_le)

theorem homogeneous_integer_box_bound (p : MvPolynomial (Fin 2) ℤ) (d : ℕ)
    (hd : 0 < d) (hp : p.IsHomogeneous d) (c : ℤ) (hc : c ≠ 0) (H : ℕ) :
    (level p c (Finset.Icc (-(H : ℤ)) H)).card ≤ d * (2 * H + 1) :=
  (integer_box_bound p c (homogeneous_constant_zero p d hd hp) hc H).trans
    (Nat.mul_le_mul_right _ hp.totalDegree_le)

end PaperP1.BivariateGridCount
