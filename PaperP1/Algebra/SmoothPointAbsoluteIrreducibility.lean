module

public import PaperP1.Algebra.FormalBranchScalarDescent
public import Mathlib.Algebra.Polynomial.Degree.Units

/-! # A rational smooth affine point forces irreducibility over every field extension

This proves the affine algebraic implication. Its connection to the actual
complex bihomogeneous polynomial in `Geometric` is a separate remaining step.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothPointAbsoluteIrreducibility

open Polynomial PaperP1.PolynomialScalarProjection PaperP1.SmoothAffineFormalBranch
  PaperP1.FormalBranchScalarDescent

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem extend_degree (P : K[X][X]) : (extend P : L[X][X]).natDegree = P.natDegree := by
  have hinj : Function.Injective (Polynomial.mapRingHom (algebraMap K L)) :=
    Polynomial.map_injective (algebraMap K L) (algebraMap K L).injective
  exact Polynomial.natDegree_map_eq_of_injective hinj P

theorem unit_of_factor_divisibility (P A B : L[X][X]) (hP : P ≠ 0)
    (hprod : P = A * B) (hdiv : P ∣ A) : IsUnit B := by
  obtain ⟨C, hC⟩ := hdiv
  have hCB : C * B = 1 := by
    apply mul_left_cancel₀ hP
    calc
      P * (C * B) = (P * C) * B := (mul_assoc _ _ _).symm
      _ = A * B := by rw [← hC]
      _ = P := hprod.symm
      _ = P * 1 := (mul_one _).symm
  exact isUnit_iff_exists_inv.mpr ⟨C, by simpa only [mul_comm] using hCB⟩

theorem irreducible_extend (P : K[X][X]) (hP : Irreducible P)
    (hdeg : 0 < P.natDegree) (x : K) (y : PowerSeries K) (hy : evaluation x y P = 0) :
    Irreducible (extend P : L[X][X]) := by
  have hdegL : 0 < (extend P : L[X][X]).natDegree := (extend_degree (L := L) P).symm ▸ hdeg
  have hne : (extend P : L[X][X]) ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hdegL
    omega
  refine ⟨Polynomial.not_isUnit_of_natDegree_pos _ hdegL, ?_⟩
  intro A B hAB
  have hprod : evaluation (algebraMap K L x) (PowerSeries.map (algebraMap K L) y) A *
      evaluation (algebraMap K L x) (PowerSeries.map (algebraMap K L) y) B = 0 := by
    rw [← map_mul, ← hAB, evaluation_naturality, hy, map_zero]
  rcases mul_eq_zero.mp hprod with hA | hB
  · right
    exact unit_of_factor_divisibility (extend P) A B hne hAB
      ((extension_kernel P hP hdeg x y hy A).mp hA)
  · left
    apply unit_of_factor_divisibility (extend P) B A hne _
      ((extension_kernel P hP hdeg x y hy B).mp hB)
    simpa only [mul_comm] using hAB

theorem smooth_point_irreducible (P : K[X][X]) (hP : Irreducible P)
    (hdeg : 0 < P.natDegree) (x z : K) (hz : P.evalEval x z = 0)
    (hd : P.derivative.evalEval x z ≠ 0) : Irreducible (extend P : L[X][X]) := by
  obtain ⟨y, _, hy⟩ := exists_branch P x z hz hd
  exact irreducible_extend P hP hdeg x y hy

theorem derivative_zero_of_reducible (P : K[X][X]) (hP : Irreducible P)
    (hdeg : 0 < P.natDegree) (hred : ¬Irreducible (extend P : L[X][X]))
    (x z : K) (hz : P.evalEval x z = 0) : P.derivative.evalEval x z = 0 := by
  by_contra hd
  exact hred (smooth_point_irreducible P hP hdeg x z hz hd)

end PaperP1.SmoothPointAbsoluteIrreducibility
