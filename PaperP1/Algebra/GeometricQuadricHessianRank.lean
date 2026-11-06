module

public import PaperP1.Algebra.DiagonalQuadricFactorization
public import PaperP1.Algebra.DiagonalQuadricHessian
public import PaperP1.Algebra.QuadraticHessianLinearTransport
public import PaperP1.Algebra.MatrixMinorRankWitness

/-! # An irreducible quadric over an algebraically closed odd-characteristic field has a nonzero actual Hessian minor -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GeometricQuadricHessianRank

open MvPolynomial HomogeneousQuadraticHessian QuadraticPolynomialDiagonalization
open scoped Classical

variable {F : Type*} [Field F] [IsAlgClosed F] [Invertible (2 : F)]

theorem rank_ge_three (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 2)
    (hirr : Irreducible P) : 3 ≤ (Matrix.of (entry P)).rank := by
  obtain ⟨w, e, he⟩ := exists_equiv P hP
  have hi : Irreducible (diagonal w) := by
    have hh := (MulEquiv.irreducible_iff (LinearMapPolynomialCoordinates.equiv e).toMulEquiv).mpr hirr
    change Irreducible (LinearMapPolynomialCoordinates.substitute e.toLinearMap P) at hh
    rw [he] at hh
    exact hh
  have hcount := DiagonalQuadricFactorization.at_least_three_nonzero w hi
  have hr := QuadraticHessianLinearTransport.rank_transport P hP e
  rw [he, DiagonalQuadricHessian.rank] at hr
  exact hcount.trans_eq hr

theorem exists_nonzero_minor (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 2)
    (hirr : Irreducible P) :
    ∃ (c r : Fin 3 → Fin 4), Matrix.det (fun i j ↦ entry P (r i) (c j)) ≠ 0 := by
  obtain ⟨c, r, hr⟩ := MatrixMinorRankWitness.exists_minor (Matrix.of (entry P)) 3 (rank_ge_three P hP hirr)
  exact ⟨c, r, hr⟩

end PaperP1.GeometricQuadricHessianRank
