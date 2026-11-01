module

public import PaperP1.Diophantine.ResultantDivisibility
public import Mathlib.Data.Fin.Rev
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Exact absolute-value symmetry of the two padded homogeneous resultants -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReflectedResultants

open Polynomial

def columnReverse (d : ℕ) : Equiv.Perm (Fin (d + d)) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (@Fin.revPerm d) (@Fin.revPerm d)).trans finSumFinEquiv)

theorem columnReverse_left (d : ℕ) (j : Fin d) :
    columnReverse d (Fin.castAdd d j) = Fin.castAdd d j.rev := by
  simp [columnReverse]

theorem columnReverse_right (d : ℕ) (j : Fin d) :
    columnReverse d (Fin.natAdd d j) = Fin.natAdd d j.rev := by
  unfold columnReverse
  rw [Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.trans_apply]
  rfl

variable {R : Type*} [Semiring R]

theorem reflected_entry (p : R[X]) (d : ℕ) (i : Fin (d + d)) (j : Fin d) :
    (if i.val ∈ Set.Icc j.val (j.val + d) then (p.reflect d).coeff (i.val - j.val) else 0) =
      (if i.rev.val ∈ Set.Icc j.rev.val (j.rev.val + d) then p.coeff (i.rev.val - j.rev.val) else 0) := by
  have hi := i.isLt
  have hj := j.isLt
  have hiff : i.val ∈ Set.Icc j.val (j.val + d) ↔
      i.rev.val ∈ Set.Icc j.rev.val (j.rev.val + d) := by
    simp only [Set.mem_Icc, Fin.val_rev]
    omega
  by_cases h : i.val ∈ Set.Icc j.val (j.val + d)
  · rw [ite_eq_left h, ite_eq_left (hiff.mp h), Polynomial.coeff_reflect,
      Polynomial.revAt_le (by obtain ⟨_, hhi⟩ := h; omega)]
    congr 1
    have hbounds := h
    simp only [Set.mem_Icc] at hbounds
    simp only [Fin.val_rev]
    omega
  · rw [ite_eq_right h, ite_eq_right (fun hr ↦ h (hiff.mpr hr))]

theorem sylvester_reflect (f g : R[X]) (d : ℕ) :
    Polynomial.sylvester (f.reflect d) (g.reflect d) d d =
      (Polynomial.sylvester f g d d).submatrix Fin.revPerm (columnReverse d) := by
  ext i j
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
  · rw [Matrix.submatrix_apply, columnReverse_left, Fin.revPerm_apply]
    simpa only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left] using reflected_entry g d i j
  · rw [Matrix.submatrix_apply, columnReverse_right, Fin.revPerm_apply]
    simpa only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right] using reflected_entry f d i j

theorem resultant_abs_reflect (f g : ℤ[X]) (d : ℕ) :
    |(f.reflect d).resultant (g.reflect d) d d| = |f.resultant g d d| := by
  unfold Polynomial.resultant
  rw [sylvester_reflect]
  exact Matrix.abs_det_submatrix_equiv_equiv Fin.revPerm (columnReverse d) _

theorem resultant_natAbs_reflect (f g : ℤ[X]) (d : ℕ) :
    ((f.reflect d).resultant (g.reflect d) d d).natAbs = (f.resultant g d d).natAbs := by
  have h := resultant_abs_reflect f g d
  simp only [Int.abs_eq_natAbs] at h
  exact_mod_cast h

theorem resultant_eq_or_neg (f g : ℤ[X]) (d : ℕ) :
    (f.reflect d).resultant (g.reflect d) d d = f.resultant g d d ∨
      (f.reflect d).resultant (g.reflect d) d d = -f.resultant g d d :=
  abs_eq_abs.mp (resultant_abs_reflect f g d)

theorem reflected_resultant_ne_zero (f g : ℤ[X]) (d : ℕ) (hR : f.resultant g d d ≠ 0) :
    (f.reflect d).resultant (g.reflect d) d d ≠ 0 := by
  apply Int.natAbs_ne_zero.mp
  rw [resultant_natAbs_reflect]
  exact Int.natAbs_ne_zero.mpr hR

theorem primitive_resultant_divisor (f g : ℤ[X]) (d : ℕ) (hd : 0 < d)
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d) (a b q : ℤ)
    (hab : a.natAbs.Coprime b.natAbs)
    (hleft : q ∣ MvPolynomial.eval ![a, b] (f.homogenize d))
    (hright : q ∣ MvPolynomial.eval ![a, b] (g.homogenize d)) : q ∣ f.resultant g d d := by
  have hpos : d ≠ 0 ∨ d ≠ 0 := Or.inl hd.ne'
  have hforward := PaperP1.ResultantDivisibility.dvd_resultant_coordinate_power f g d d hf hg hpos a b q hleft hright
  have hfr : (f.reflect d).natDegree ≤ d := Polynomial.natDegree_reflect_le.trans_eq (max_eq_left hf)
  have hgr : (g.reflect d).natDegree ≤ d := Polynomial.natDegree_reflect_le.trans_eq (max_eq_left hg)
  have hlr : q ∣ MvPolynomial.eval ![b, a] ((f.reflect d).homogenize d) := by
    rw [PaperP1.ResultantDivisibility.eval_reflected_homogenize f d hf b a]
    exact hleft
  have hrr : q ∣ MvPolynomial.eval ![b, a] ((g.reflect d).homogenize d) := by
    rw [PaperP1.ResultantDivisibility.eval_reflected_homogenize g d hg b a]
    exact hright
  have hreverse := PaperP1.ResultantDivisibility.dvd_resultant_coordinate_power
    (f.reflect d) (g.reflect d) d d hfr hgr hpos b a q hlr hrr
  have ha := Int.natAbs_dvd_natAbs.mpr hreverse
  have hb := Int.natAbs_dvd_natAbs.mpr hforward
  simp only [Int.natAbs_mul, Int.natAbs_pow, resultant_natAbs_reflect] at ha hb
  have hdiv := Nat.dvd_gcd ha hb
  rw [Nat.gcd_mul_left, (hab.pow (d + d) (d + d)).gcd_eq_one, mul_one] at hdiv
  exact Int.natAbs_dvd_natAbs.mp hdiv

end PaperP1.ReflectedResultants
