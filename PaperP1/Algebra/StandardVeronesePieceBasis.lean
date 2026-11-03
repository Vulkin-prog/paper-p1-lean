module

public import PaperP1.Algebra.MvPolynomialHomogeneousBasis
public import PaperP1.Algebra.SourceVeroneseGrading
public import PaperP1.Algebra.HomogeneousSplitRadicalVeroneseTowerData

/-! # Literal monomial bases of the actual native Veronese and its rescaled pieces -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.StandardVeronesePieceBasis

open Module PaperP1.SourceVeroneseGrading PaperP1.HomogeneousSplitRadicalVeroneseTowerData

attribute [local instance] MvPolynomial.gradedAlgebra

def pieceEquiv (F : Type*) [Field F] (D n : ℕ) :
    nativePiece F D n ≃ₗ[F] MvPolynomial.homogeneousSubmodule (Fin 3) F (n * D) where
  toFun x := ⟨((x : Base F D) : MvPolynomial (Fin 3) F), x.property⟩
  invFun p := ⟨⟨p, GradedVeroneseAlgebra.piece_mem
    (MvPolynomial.homogeneousSubmodule (Fin 3) F) D n p.property⟩, p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pieceEquiv_val (F : Type*) [Field F] (D n : ℕ) (x : nativePiece F D n) :
    (pieceEquiv F D n x : MvPolynomial (Fin 3) F) = ((x : Base F D) : MvPolynomial (Fin 3) F) := rfl

def pieceBasis (F : Type*) [Field F] (D n : ℕ) :
    Basis {d : Fin 3 →₀ ℕ // d.degree = n * D} F (nativePiece F D n) :=
  (MvPolynomialHomogeneousBasis.pieceBasis F (Fin 3) (n * D)).map (pieceEquiv F D n).symm

theorem pieceBasis_apply (F : Type*) [Field F] (D n : ℕ)
    (d : {d : Fin 3 →₀ ℕ // d.degree = n * D}) :
    (((pieceBasis F D n d : nativePiece F D n) : Base F D) : MvPolynomial (Fin 3) F) =
      MvPolynomial.monomial d.1 1 := by
  rw [pieceBasis, Basis.map_apply]
  exact MvPolynomialHomogeneousBasis.pieceBasis_apply F (Fin 3) (n * D) d

def basis (F : Type*) [Field F] (D : ℕ) (hD : 0 < D) :
    Basis (Σ n : ℕ, {d : Fin 3 →₀ ℕ // d.degree = n * D}) F (Base F D) := by
  let := nativeGrading F D hD
  exact (DirectSum.Decomposition.isInternal (nativePiece F D)).collectedBasis (pieceBasis F D)

theorem basis_mem (F : Type*) [Field F] (D : ℕ) (hD : 0 < D)
    (i : Σ n : ℕ, {d : Fin 3 →₀ ℕ // d.degree = n * D}) :
    basis F D hD i ∈ nativePiece F D i.1 := by
  let := nativeGrading F D hD
  exact (DirectSum.Decomposition.isInternal (nativePiece F D)).collectedBasis_mem (pieceBasis F D) i

theorem basis_val (F : Type*) [Field F] (D : ℕ) (hD : 0 < D)
    (i : Σ n : ℕ, {d : Fin 3 →₀ ℕ // d.degree = n * D}) :
    (basis F D hD i : MvPolynomial (Fin 3) F) = MvPolynomial.monomial i.2.1 1 := by
  let := nativeGrading F D hD
  rw [basis, DirectSum.IsInternal.collectedBasis_coe]
  exact pieceBasis_apply F D i.1 i.2

end PaperP1.StandardVeronesePieceBasis
