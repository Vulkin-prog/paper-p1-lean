module

public import PaperP1.Geometry.FiniteCurvePrimitiveCoordinate
public import PaperP1.Geometry.LinearHypersurfaceMinimalEquation
public import PaperP1.Geometry.LinearHypersurfaceImageFiber
public import PaperP1.Geometry.LinearHypersurfaceImageBirational
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.FieldTheory.Perfect

/-! # A genuine finite linear normalization supplies a bounded integer birational hypersurface projection -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedHomogeneousHypersurfaceProjection

open MvPolynomial LinearHypersurfaceImage

theorem exists_projection {F A : Type*} [Field F] [CharZero F] [CommRing A] [IsDomain A]
    [Algebra F A] {m n : ℕ} (H : ℕ → Submodule F A) [GradedAlgebra H]
    (x : Fin n → A) (hx : ∀ i, x i ∈ H 1) (hgen : Algebra.adjoin F (Set.range x) = ⊤)
    (g : Fin m → A) (hg : ∀ i, g i ∈ H 1) (hfinite : (aeval (R := F) g).Finite)
    (hinj : Function.Injective (aeval (R := F) g)) (d : ℕ) (hd : 0 < d)
    (hrank : letI : Algebra (MvPolynomial (Fin m) F) A := (aeval (R := F) g).toRingHom.toAlgebra;
      Module.finrank (MvPolynomial (Fin m) F) A = d) :
    ∃ (u : Fin n → ℕ) (q : MvPolynomial (Fin (m + 1)) F) (δ : A),
      (∀ i, u i ≤ ((n - 1) * d ^ 2 + 1) ^ (n - 1)) ∧
      let y := aeval (R := F) x (CommonLinearNormalization.form (fun i ↦ (u i : F)));
      ideal (F := F) g y = Ideal.span {q} ∧ Irreducible q ∧ q.IsHomogeneous d ∧ q.totalDegree = d ∧
      (finSuccEquiv F m q).Monic ∧
      (letI : Algebra (CoordinateRing (F := F) g y) A := (toSource g y).toRingHom.toAlgebra;
        Module.finrank (CoordinateRing (F := F) g y) A = 1) ∧
      δ = aeval (R := F) (coordinates g y) (pderiv 0 q) ∧
      δ ∈ H (d - 1) ∧ δ ≠ 0 ∧ (∀ a : A, δ * a ∈ (toSource (F := F) g y).range) ∧
      ∀ (N : ℕ) (v : Fin n → ℤ), (∀ i, (v i).natAbs ≤ N) →
        |eval v (CommonLinearNormalization.form (fun i ↦ (u i : ℤ)))| ≤
          ((n * (((n - 1) * d ^ 2 + 1) ^ (n - 1)) * N : ℕ) : ℤ) := by
  let R := MvPolynomial (Fin m) F
  let : Algebra R A := (aeval (R := F) g).toRingHom.toAlgebra
  let : IsScalarTower F R A := IsScalarTower.of_algebraMap_eq (fun r ↦ (aeval (R := F) g).commutes r |>.symm)
  let K := FractionRing R
  let L := FractionRing A
  let : Algebra R L := inferInstance
  let : IsScalarTower R A L := inferInstance
  let : Algebra F L := inferInstance
  let : IsScalarTower F A L := inferInstance
  let : Algebra F K := inferInstance
  let : IsScalarTower F R K := inferInstance
  have hsource : algebraMap R A = (aeval (R := F) g).toRingHom := rfl
  have hmapinj : Function.Injective (algebraMap R A) := by rw [hsource]; exact hinj
  let : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective _ _).mpr hmapinj
  let : Module.IsTorsionFree R A := inferInstance
  let : FaithfulSMul R L :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr ((IsFractionRing.injective A L).comp hmapinj)
  let : Algebra K L := FractionRing.liftAlgebra R L
  let : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  let : IsScalarTower F R L := IsScalarTower.to₁₂₄ F R A L
  let : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq (fun r ↦ by
    rw [IsScalarTower.algebraMap_apply F R K, ← IsScalarTower.algebraMap_apply R K L]
    exact IsScalarTower.algebraMap_apply F R L r)
  let : CharZero K := Algebra.charZero_of_charZero F K
  have hdegree : Module.finrank K L = d := (IsFractionRing.finrank_eq R K A L).trans hrank
  let : FiniteDimensional K L := Module.finite_of_finrank_pos (by rw [hdegree]; exact hd)
  let : Algebra.IsSeparable K L := inferInstance
  obtain ⟨u, hu, hprimitive, _hmin, hheight⟩ := FiniteCurvePrimitiveCoordinate.exists_coordinate
    (F := F) (R := R) (A := A) (K := K) (L := L) d hd hrank n x hgen
  let y := aeval (R := F) x (CommonLinearNormalization.form (fun i ↦ (u i : F)))
  have hy : y ∈ H 1 := GradedPolynomialGenerators.eval_homogeneous H x hx 1 _
    (CommonLinearNormalization.form_homogeneous _)
  have hint : IsIntegral R y := by
    let : Module.Finite R A := hfinite
    exact IsIntegral.of_finite R y
  have he := LinearHypersurfaceMinimalEquation.equation_degree_of_primitive H g hg y hy
    hsource hint hprimitive
  have he' := LinearHypersurfaceMinimalEquation.equation_totalDegree H g hg y hy hsource hint
  have hdmin : (minpoly R y).natDegree = d := he'.symm.trans (he.trans hdegree)
  let q := LinearHypersurfaceMinimalEquation.equation (m := m) (F := F) y
  have hqhom : q.IsHomogeneous d := by
    rw [← hdmin]
    exact LinearHypersurfaceMinimalEquation.equation_homogeneous H g hg y hy hsource hint
  refine ⟨u, q, LinearHypersurfaceImageFiber.denominator (m := m) (F := F) y, hu,
    LinearHypersurfaceMinimalEquation.principal g y hsource hint,
    LinearHypersurfaceMinimalEquation.equation_irreducible g y hsource hint,
    hqhom, he.trans hdegree, LinearHypersurfaceMinimalEquation.equation_monic y hint,
    ?_, ?_, ?_, ?_, ?_, hheight⟩
  · exact LinearHypersurfaceImageBirational.rank_one g y K L hsource hprimitive
  · exact LinearHypersurfaceImageFiber.denominator_is_partial g y hsource
  · exact LinearHypersurfaceImageFiber.denominator_homogeneous H g hg y hy hsource d hqhom
  · exact LinearHypersurfaceImageFiber.denominator_ne_zero (K := K) (L := L) g y hsource hfinite
  · exact LinearHypersurfaceImageFiber.conductor g y hsource hfinite hprimitive

end PaperP1.BoundedHomogeneousHypersurfaceProjection
