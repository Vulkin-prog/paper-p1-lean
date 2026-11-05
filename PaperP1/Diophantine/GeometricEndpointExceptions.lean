module

public import PaperP1.Diophantine.PrimitiveHomogeneousRootBound
public import PaperP1.Diophantine.GeometricBiformCoarseCount

/-! # The endpoint zero fibres form a degree-uniform exceptional population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GeometricEndpointExceptions

open Polynomial Finset PaperP1.BivariateDegrees PaperP1.BidegreeOneFibreCount
open PaperP1.RationalBivariateIrreducibility PaperP1.GeometricFactorSwap

theorem constant_coefficient_ne_zero (G : ℤ[X][X]) (hne : G ≠ 0)
    (hgeom : Geometric G) (hx : 0 < degreeX G) : G.coeff 0 ≠ 0 := by
  let P := rationalize (Bivariate.swap G)
  have hswap : Bivariate.swap G ≠ 0 := by
    intro hz
    apply hne
    exact (Bivariate.swap (R := ℤ)).injective (hz.trans (map_zero _).symm)
  have hP : Irreducible P := ScalarIrreducibilityReflection.geometric_rational_irreducible
    (Bivariate.swap G) hswap (geometric_swap G hgeom)
  have hd : 0 < P.natDegree := by
    rw [RationalizedCriticalPointBound.outer_degree, BivariateProjectiveSwap.degreeY_swap]
    exact hx
  have hs := RationalCurveCriticalPoints.specialization_nonzero P hP hd 0
  intro hzero
  apply hs
  ext i
  simp only [P, rationalize, Polynomial.coeff_map, Polynomial.coe_evalRingHom,
    ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coe_mapRingHom, BivariateIrreducibleHomogenization.swap_coefficient,
    hzero, Polynomial.coeff_zero, map_zero]

theorem endpoint_form_nonzero (G : ℤ[X][X]) (j : ℕ) (hj : G.coeff j ≠ 0) :
    (G.coeff j).homogenize (degreeX G) ≠ 0 := by
  intro hz
  exact hj (Polynomial.eq_zero_of_homogenize_eq_zero (natDegree_coeff_le_degreeX G j) hz)

theorem one_endpoint_card (G : ℤ[X][X]) (hne : G ≠ 0) (hgeom : Geometric G)
    (hy : 0 < degreeY G) (j : ℕ) (hj : G.coeff j ≠ 0) (S : Finset Point)
    (hprim : ∀ z ∈ S, (z.1 0).natAbs.Coprime (z.1 1).natAbs ∧
      (z.2 0).natAbs.Coprime (z.2 1).natAbs)
    (hcurve : ∀ z ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1
      (IntegerFactorProjectiveCurve.projective G) = 0)
    (hend : ∀ z ∈ S, MvPolynomial.eval z.1 ((G.coeff j).homogenize (degreeX G)) = 0) :
    S.card ≤ 4 * (degreeX G + 1) * (degreeY G + 1) := by
  classical
  have hc := PrimitiveHomogeneousZeros.primitive_card ((G.coeff j).homogenize (degreeX G))
    (Polynomial.isHomogeneous_homogenize _) (endpoint_form_nonzero G j hj) (S.image Prod.fst)
    (by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
      exact (hprim z hz).1)
    (by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
      exact hend z hz)
  calc
    _ ≤ (S.image Prod.fst).card * (2 * (degreeY G + 1)) :=
      GeometricBiformCoarseCount.finite_count G hne hy hgeom S hprim hcurve
    _ ≤ (2 * (degreeX G + 1)) * (2 * (degreeY G + 1)) := Nat.mul_le_mul_right _ hc
    _ = _ := by ring

def exceptional (G : ℤ[X][X]) (S : Finset Point) : Finset Point :=
  S.filter (fun z ↦ MvPolynomial.eval z.1 ((G.coeff 0).homogenize (degreeX G)) = 0 ∨
    MvPolynomial.eval z.1 ((G.coeff (degreeY G)).homogenize (degreeX G)) = 0)

theorem exceptional_card (G : ℤ[X][X]) (hne : G ≠ 0) (hgeom : Geometric G)
    (hx : 0 < degreeX G) (hy : 0 < degreeY G) (S : Finset Point)
    (hprim : ∀ z ∈ S, (z.1 0).natAbs.Coprime (z.1 1).natAbs ∧
      (z.2 0).natAbs.Coprime (z.2 1).natAbs)
    (hcurve : ∀ z ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1
      (IntegerFactorProjectiveCurve.projective G) = 0) :
    (exceptional G S).card ≤ 8 * (degreeX G + 1) * (degreeY G + 1) := by
  classical
  have hcoeff : G.coeff (degreeY G) ≠ 0 := by
    rw [degreeY, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hne
  have hc (j : ℕ) (hj : G.coeff j ≠ 0) := one_endpoint_card G hne hgeom hy j hj
    (S.filter (fun z ↦ MvPolynomial.eval z.1 ((G.coeff j).homogenize (degreeX G)) = 0))
    (fun z hz ↦ hprim z (mem_filter.mp hz).1) (fun z hz ↦ hcurve z (mem_filter.mp hz).1)
    (fun _ hz ↦ (mem_filter.mp hz).2)
  have hset : exceptional G S =
      (S.filter (fun z ↦ MvPolynomial.eval z.1 ((G.coeff 0).homogenize (degreeX G)) = 0)) ∪
      (S.filter (fun z ↦ MvPolynomial.eval z.1 ((G.coeff (degreeY G)).homogenize (degreeX G)) = 0)) := by
    ext z
    simp only [exceptional, mem_filter, mem_union]
    tauto
  rw [hset]
  calc
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ 4 * (degreeX G + 1) * (degreeY G + 1) +
        4 * (degreeX G + 1) * (degreeY G + 1) :=
      Nat.add_le_add (hc 0 (constant_coefficient_ne_zero G hne hgeom hx)) (hc _ hcoeff)
    _ = _ := by ring

theorem height_split (G : ℤ[X][X]) (hne : G ≠ 0) (hgeom : Geometric G)
    (hx : 0 < degreeX G) (hy : 0 < degreeY G) (S : Finset Point)
    (hprim : ∀ z ∈ S, (z.1 0).natAbs.Coprime (z.1 1).natAbs ∧
      (z.2 0).natAbs.Coprime (z.2 1).natAbs)
    (hcurve : ∀ z ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1
      (IntegerFactorProjectiveCurve.projective G) = 0)
    (L : ℝ) (hL : 0 ≤ L) (hbox : ∀ z ∈ S, ∀ c, |(z.1 c : ℝ)| ≤ L) :
    (exceptional G S).card ≤ 8 * (degreeX G + 1) * (degreeY G + 1) ∧
      ∀ z ∈ S \ exceptional G S, ∀ c,
        |(z.2 c : ℝ)| ≤ (degreeX G + 1) * (BivariateHeight.height G : ℝ) * L ^ degreeX G := by
  classical
  refine ⟨exceptional_card G hne hgeom hx hy S hprim hcurve, ?_⟩
  intro z hz
  have hzS := (mem_sdiff.mp hz).1
  have he : ¬(MvPolynomial.eval z.1 ((G.coeff 0).homogenize (degreeX G)) = 0 ∨
      MvPolynomial.eval z.1 ((G.coeff (degreeY G)).homogenize (degreeX G)) = 0) := by
    intro h
    exact (mem_sdiff.mp hz).2 (mem_filter.mpr ⟨hzS, h⟩)
  exact PrimitiveHomogeneousRootBound.fibre_height_bound G z.1 z.2 (hprim z hzS).2
    (hcurve z hzS) (fun h ↦ he (Or.inl h)) (fun h ↦ he (Or.inr h)) L hL (hbox z hzS)

end PaperP1.GeometricEndpointExceptions
