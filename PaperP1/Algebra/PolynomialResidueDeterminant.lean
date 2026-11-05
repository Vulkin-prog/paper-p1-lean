module

public import PaperP1.Algebra.FilteredEvaluationDeterminantDivisibility
public import Mathlib.Algebra.Polynomial.Taylor

/-! # Polynomial evaluations in one residue class have a triangular determinant divisor -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialResidueDeterminant

open Polynomial Finset PaperP1.WeightedEvaluationDeterminant
  PaperP1.FilteredEvaluationDeterminantDivisibility

variable {R : Type*} [CommRing R]

theorem polynomial_evaluation_dvd (p : R) (k : ℕ) (P : Fin k → R[X]) (x : Fin k → R)
    (hx : ∀ j, p ∣ x j) : p ^ (k * (k - 1) / 2) ∣ Matrix.det (fun i j ↦ (P i).eval (x j)) := by
  classical
  let M := (univ : Finset (Fin k)).sup (fun i ↦ (P i).natDegree) + 1
  have hd (i : Fin k) : (P i).natDegree < M := by
    have hle := Finset.le_sup (f := fun i ↦ (P i).natDegree) (mem_univ i)
    omega
  let C : Fin k → Fin M → R := fun i r ↦ (P i).coeff r.val
  let V : Fin M → Fin k → R := fun r j ↦ x j ^ r.val
  have hV : ∀ r j, p ^ r.val ∣ V r j := by
    intro r j
    obtain ⟨a, ha⟩ := hx j
    refine ⟨a ^ r.val, ?_⟩
    change x j ^ r.val = p ^ r.val * a ^ r.val
    rw [ha, mul_pow]
  have he : evaluationMatrix C V = (fun i j ↦ (P i).eval (x j)) := by
    ext i j
    change (∑ r : Fin M, (P i).coeff r.val * x j ^ r.val) = (P i).eval (x j)
    calc
      _ = ∑ r ∈ range M, (P i).coeff r * x j ^ r := by
        apply Finset.sum_bij (fun r _hr ↦ r.val)
        · intro r _hr
          exact mem_range.mpr r.isLt
        · intro r _hr s _hs heq
          exact Fin.ext heq
        · intro r hr
          exact ⟨⟨r, mem_range.mp hr⟩, mem_univ _, rfl⟩
        · intro r _hr
          rfl
      _ = _ := (Polynomial.eval_eq_sum_range' (hd i) (x j)).symm
  rw [← he]
  exact evaluation_triangular_dvd p k M C V hV

theorem congruent_polynomial_evaluation_dvd (p : R) (k : ℕ) (P : Fin k → R[X])
    (x : Fin k → R) (A : Matrix (Fin k) (Fin k) R) (hx : ∀ j, p ∣ x j)
    (hA : ∀ i j, p ^ (k * (k - 1) / 2) ∣ A i j - (P i).eval (x j)) :
    p ^ (k * (k - 1) / 2) ∣ A.det := by
  have hd := determinant_congruence_dvd (p ^ (k * (k - 1) / 2)) A
    (fun i j ↦ (P i).eval (x j)) hA
  have hs := dvd_add hd (polynomial_evaluation_dvd p k P x hx)
  simpa only [sub_add_cancel] using hs

theorem same_residue_evaluation_dvd (p a : R) (k : ℕ) (P : Fin k → R[X]) (x : Fin k → R)
    (hx : ∀ j, p ∣ x j - a) :
    p ^ (k * (k - 1) / 2) ∣ Matrix.det (fun i j ↦ (P i).eval (x j)) := by
  have h := polynomial_evaluation_dvd p k (fun i ↦ Polynomial.taylor a (P i))
    (fun j ↦ x j - a) hx
  simpa only [Polynomial.taylor_eval_sub] using h

theorem zero_of_small (p k : ℕ) (A : Matrix (Fin k) (Fin k) ℤ)
    (hdiv : (p : ℤ) ^ (k * (k - 1) / 2) ∣ A.det)
    (hsmall : A.det.natAbs < p ^ (k * (k - 1) / 2)) : A.det = 0 := by
  by_contra hn
  have hb := Int.natAbs_le_of_dvd_ne_zero hdiv hn
  simp only [Int.natAbs_pow, Int.natAbs_natCast] at hb
  omega

end PaperP1.PolynomialResidueDeterminant
