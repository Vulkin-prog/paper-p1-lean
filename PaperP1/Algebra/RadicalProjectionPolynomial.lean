module

public import PaperP1.Algebra.BirationalRadicalProjection
public import Mathlib.FieldTheory.Minpoly.Finite
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The actual image is cut out by one monic irreducible radical-sum polynomial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RadicalProjectionPolynomial

open Polynomial PaperP1.FiniteQuadraticTower PaperP1.FiniteRadicalProjection
  PaperP1.QuadraticTowerBaseChange PaperP1.QuadraticTowerSumBaseChange

def equation (R : Type*) [CommRing R] (s : List R) : R[X] := minpoly R (radicalSum R s)

theorem equation_monic (R : Type*) [CommRing R] (s : List R) : (equation R s).Monic :=
  minpoly.monic (sum_integral R s)

theorem equation_root (R : Type*) [CommRing R] (s : List R) :
    aeval (radicalSum R s) (equation R s) = 0 := minpoly.aeval R (radicalSum R s)

theorem map_aeval {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (s : List R) (P : R[X]) :
    (mapData φ s).hom (aeval (radicalSum R s) P) = aeval (radicalSum S (s.map φ)) (P.map φ) := by
  have hcomm : (algebraMap S (Tower S (s.map φ))).comp φ =
      (mapData φ s).hom.comp (algebraMap R (Tower R s)) := by
    ext r
    exact ((mapData φ s).commutes r).symm
  simpa only [map_radicalSum] using map_aeval_eq_aeval_map hcomm P (radicalSum R s)

theorem annihilating_degree_lower (R K : Type*) [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K] (s : List R)
    (hs : IndependentQuadraticTower.Independent (s.map (algebraMap R K)))
    (P : R[X]) (hP : P ≠ 0) (hroot : aeval (radicalSum R s) P = 0) : 2 ^ s.length ≤ P.natDegree := by
  let : Field (Tower K (s.map (algebraMap R K))) := (IndependentQuadraticTower.isField K _ hs).toField
  have hzero : aeval (radicalSum K (s.map (algebraMap R K))) (P.map (algebraMap R K)) = 0 := by
    rw [← map_aeval, hroot, map_zero]
  have hle := natDegree_le_of_dvd (minpoly.dvd K _ hzero)
    ((Polynomial.map_ne_zero_iff (IsFractionRing.injective R K)).mpr hP)
  simpa only [PrimitiveRadicalSum.minpoly_degree, List.length_map,
    natDegree_map_eq_of_injective (IsFractionRing.injective R K)] using hle

theorem equation_degree (R K : Type*) [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K] (s : List R)
    (hs : IndependentQuadraticTower.Independent (s.map (algebraMap R K))) :
    (equation R s).natDegree = 2 ^ s.length := by
  have hle := minpoly.natDegree_le (A := R) (radicalSum R s)
  rw [FiniteQuadraticTower.finrank] at hle
  exact le_antisymm hle (annihilating_degree_lower R K s hs _ (equation_monic R s).ne_zero (equation_root R s))

theorem mapped_equation (R K : Type*) [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K] (s : List R)
    (hs : IndependentQuadraticTower.Independent (s.map (algebraMap R K))) :
    (equation R s).map (algebraMap R K) = minpoly K (radicalSum K (s.map (algebraMap R K))) := by
  let : Field (Tower K (s.map (algebraMap R K))) := (IndependentQuadraticTower.isField K _ hs).toField
  have hzero : aeval (radicalSum K (s.map (algebraMap R K))) ((equation R s).map (algebraMap R K)) = 0 := by
    rw [← map_aeval, equation_root, map_zero]
  apply eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (sum_integral K _))
    ((equation_monic R s).map _) (minpoly.dvd K _ hzero)
  rw [natDegree_map_eq_of_injective (IsFractionRing.injective R K), equation_degree R K s hs,
    PrimitiveRadicalSum.minpoly_degree, List.length_map]

theorem root_iff_dvd (R K : Type*) [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K] (s : List R)
    (hs : IndependentQuadraticTower.Independent (s.map (algebraMap R K))) (P : R[X]) :
    aeval (radicalSum R s) P = 0 ↔ equation R s ∣ P := by
  constructor
  · intro hz
    let : Field (Tower K (s.map (algebraMap R K))) := (IndependentQuadraticTower.isField K _ hs).toField
    have hzero : aeval (radicalSum K (s.map (algebraMap R K))) (P.map (algebraMap R K)) = 0 := by
      rw [← map_aeval, hz, map_zero]
    have hdvd := minpoly.dvd K _ hzero
    rw [← mapped_equation R K s hs] at hdvd
    exact (map_dvd_map _ (IsFractionRing.injective R K) (equation_monic R s)).mp hdvd
  · rintro ⟨Q, rfl⟩
    rw [map_mul, equation_root, zero_mul]

theorem equation_irreducible (R K : Type*) [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K] (s : List R)
    (hs : IndependentQuadraticTower.Independent (s.map (algebraMap R K))) : Irreducible (equation R s) := by
  let : Field (Tower K (s.map (algebraMap R K))) := (IndependentQuadraticTower.isField K _ hs).toField
  have : IsDomain (Tower R s) := source_isDomain (algebraMap R K) (IsFractionRing.injective R K) s inferInstance
  exact minpoly.irreducible (sum_integral R s)

theorem kernel_eq_span (R K : Type*) [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K] (s : List R)
    (hs : IndependentQuadraticTower.Independent (s.map (algebraMap R K))) :
    RingHom.ker (aeval (radicalSum R s)) = Ideal.span {equation R s} := by
  ext P
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  exact root_iff_dvd R K s hs P

def quotientEquivImage (R K : Type*) [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K] (s : List R)
    (hs : IndependentQuadraticTower.Independent (s.map (algebraMap R K))) :
    (R[X] ⧸ Ideal.span {equation R s}) ≃ₐ[R] imageAlgebra R s := by
  let ψ : R[X] →ₐ[R] Tower R s := aeval (radicalSum R s)
  let e₁ : (R[X] ⧸ Ideal.span {equation R s}) ≃ₐ[R] (R[X] ⧸ RingHom.ker ψ) :=
    Ideal.quotientEquivAlgOfEq R (kernel_eq_span R K s hs).symm
  let e₂ : (R[X] ⧸ RingHom.ker ψ) ≃ₐ[R] ψ.range := Ideal.quotientKerEquivRange ψ
  let e₃ : ψ.range ≃ₐ[R] imageAlgebra R s := Subalgebra.equivOfEq _ _ (image_eq_range R s).symm
  exact e₁.trans (e₂.trans e₃)

theorem quotientEquivImage_apply (R K : Type*) [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K] (s : List R)
    (hs : IndependentQuadraticTower.Independent (s.map (algebraMap R K))) (P : R[X]) :
    (quotientEquivImage R K s hs (Ideal.Quotient.mk _ P) : Tower R s) = aeval (radicalSum R s) P := rfl

end PaperP1.RadicalProjectionPolynomial
