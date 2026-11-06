module

public import PaperP1.Algebra.GeometricQuadricHessianRank
public import PaperP1.Algebra.QuadricHessianIrreducibility
public import PaperP1.Arithmetic.QuadricHessianMinorHeight
public import PaperP1.Arithmetic.P3FiniteFieldClassEstimate

/-! # An actual nonzero integer Hessian minor is a bounded geometric good-reduction certificate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadricHessianGoodReduction

open MvPolynomial HomogeneousQuadraticHessian QuadricHessianMinorHeight
open scoped Classical

theorem map_minor {F : Type*} [Field F] (φ : ℤ →+* F)
    (P : MvPolynomial (Fin 4) ℤ) (r c : Fin 3 → Fin 4) :
    Matrix.det (fun i j ↦ entry (map φ P) (r i) (c j)) = φ (minor P r c) := by
  let M : Matrix (Fin 3) (Fin 3) ℤ := fun i j ↦ entry P (r i) (c j)
  calc
    _ = (φ.mapMatrix M).det := by
      congr 1
      ext i j
      exact map_entry φ P (r i) (c j)
    _ = _ := (φ.map_det M).symm

theorem exists_integer_minor (P : MvPolynomial (Fin 4) ℤ) (hP : P.IsHomogeneous 2)
    (hgeom : Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) (map (Int.castRingHom ℚ) P))) :
    ∃ (r c : Fin 3 → Fin 4), minor P r c ≠ 0 := by
  let : Invertible (2 : AlgebraicClosure ℚ) := invertibleOfNonzero (by norm_num)
  have hcomp : (algebraMap ℚ (AlgebraicClosure ℚ)).comp (Int.castRingHom ℚ) =
      Int.castRingHom (AlgebraicClosure ℚ) := Subsingleton.elim _ _
  rw [map_map, hcomp] at hgeom
  obtain ⟨c, r, hr⟩ := GeometricQuadricHessianRank.exists_nonzero_minor
    (map (Int.castRingHom (AlgebraicClosure ℚ)) P) (hP.map _) hgeom
  refine ⟨r, c, ?_⟩
  intro hz
  apply hr
  rw [map_minor, hz, map_zero]

theorem geometric_reduction (p : ℕ) (hp : p.Prime) (P : MvPolynomial (Fin 4) ℤ)
    (hP : P.IsHomogeneous 2) (r c : Fin 3 → Fin 4) (hgood : ¬(p : ℤ) ∣ minor P r c) :
    P3FiniteFieldClassEstimate.GeometricReduction p hp P := by
  let : Fact p.Prime := ⟨hp⟩
  let φ := Int.castRingHom (ZMod p)
  let ψ := (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).comp φ
  have hφ : φ (minor P r c) ≠ 0 := by
    intro hz
    exact hgood ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz)
  have hψ : ψ (minor P r c) ≠ 0 := by
    intro hz
    apply hφ
    exact (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective (hz.trans (map_zero _).symm)
  change Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) (map φ P))
  rw [map_map]
  apply QuadricHessianIrreducibility.irreducible_of_nonzero_minor _ (hP.map ψ) r c
  rw [map_minor ψ]
  exact hψ

theorem bounded_certificate (A : ℕ) (P : MvPolynomial (Fin 4) ℤ) (hP : P.IsHomogeneous 2)
    (hgeom : Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) (map (Int.castRingHom ℚ) P)))
    (hcoef : ∀ m, |P.coeff m| ≤ (A : ℤ)) :
    ∃ z : ℤ, z ≠ 0 ∧ z.natAbs ≤ 48 * A ^ 3 ∧
      ∀ (p : ℕ) (hp : p.Prime), ¬(p : ℤ) ∣ z → P3FiniteFieldClassEstimate.GeometricReduction p hp P := by
  obtain ⟨r, c, hminor⟩ := exists_integer_minor P hP hgeom
  exact ⟨minor P r c, hminor, minor_bound A P hcoef r c,
    fun p hp hgood ↦ geometric_reduction p hp P hP r c hgood⟩

end PaperP1.QuadricHessianGoodReduction
