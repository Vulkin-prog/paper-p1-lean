module

public import PaperP1.Diophantine.SmoothResidueClasses
public import PaperP1.Diophantine.GeometricBiformCoarseCount

/-! # The zero denominator-and-derivative product has a degree-only population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectivePrimeExceptions

open Polynomial Finset PaperP1.BidegreeOneFibreCount PaperP1.BivariateDegrees

theorem first_axis_card (G : ℤ[X][X]) (hne : G ≠ 0)
    (hgeom : GeometricFactorSwap.Geometric G) (hy : 0 < degreeY G) (S : Finset Point)
    (hprim : ∀ z ∈ S, (z.1 0).natAbs.Coprime (z.1 1).natAbs ∧
      (z.2 0).natAbs.Coprime (z.2 1).natAbs)
    (hcurve : ∀ z ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1
      (IntegerFactorProjectiveCurve.projective G) = 0)
    (haxis : ∀ z ∈ S, z.1 1 = 0) : S.card ≤ 4 * (degreeY G + 1) := by
  classical
  have hc := PrimitiveDirections.axis_card (S.image Prod.fst)
    (by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
      exact (hprim z hz).1)
    (by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
      exact haxis z hz)
  have hb := GeometricBiformCoarseCount.finite_count G hne hy hgeom S hprim hcurve
  exact hb.trans ((Nat.mul_le_mul_right _ hc).trans_eq (by ring))

theorem second_axis_card (G : ℤ[X][X]) (hne : G ≠ 0)
    (hgeom : GeometricFactorSwap.Geometric G) (hx : 0 < degreeX G) (S : Finset Point)
    (hprim : ∀ z ∈ S, (z.1 0).natAbs.Coprime (z.1 1).natAbs ∧
      (z.2 0).natAbs.Coprime (z.2 1).natAbs)
    (hcurve : ∀ z ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1
      (IntegerFactorProjectiveCurve.projective G) = 0)
    (haxis : ∀ z ∈ S, z.2 1 = 0) : S.card ≤ 4 * (degreeX G + 1) := by
  classical
  have hswap : Bivariate.swap G ≠ 0 := by
    intro hz
    apply hne
    exact (Bivariate.swap (R := ℤ)).injective (hz.trans (map_zero _).symm)
  have hc := first_axis_card (Bivariate.swap G) hswap (GeometricFactorSwap.geometric_swap G hgeom)
    (by rw [BivariateProjectiveSwap.degreeY_swap]; exact hx) (S.image Prod.swap)
    (by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
      exact ⟨(hprim z hz).2, (hprim z hz).1⟩)
    (by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
      rw [BivariateProjectiveSwap.evaluation_swap]
      exact hcurve z hz)
    (by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
      exact haxis z hz)
  rw [Finset.card_image_of_injective _ Prod.swap_injective, BivariateProjectiveSwap.degreeY_swap] at hc
  exact hc

theorem critical_card (G : ℤ[X][X]) (hne : G ≠ 0)
    (hgeom : GeometricFactorSwap.Geometric G) (hy : 0 < degreeY G) (S : Finset Point)
    (hprim : ∀ z ∈ S, (z.1 0).natAbs.Coprime (z.1 1).natAbs ∧
      (z.2 0).natAbs.Coprime (z.2 1).natAbs)
    (hcurve : ∀ z ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1
      (IntegerFactorProjectiveCurve.projective G) = 0)
    (hden : ∀ z ∈ S, z.1 1 ≠ 0 ∧ z.2 1 ≠ 0)
    (hder : ∀ z ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1
      (IntegerFactorProjectiveCurve.projective G.derivative) = 0) :
    S.card ≤ 8 * degreeX G * degreeY G ^ 2 := by
  apply PrimitiveRationalPointLift.primitive_critical_points_card G
    (ScalarIrreducibilityReflection.geometric_rational_irreducible G hne hgeom) hy S hprim hden
  intro z hz
  refine ⟨(NonGeometricRationalSingularity.projective_zero_iff G z.1 z.2
    (hden z hz).1 (hden z hz).2).mp (hcurve z hz), ?_⟩
  have hd := (NonGeometricRationalSingularity.projective_zero_iff G.derivative z.1 z.2
    (hden z hz).1 (hden z hz).2).mp (hder z hz)
  simpa only [RationalBivariateIrreducibility.rationalize, Polynomial.derivative_map] using hd

theorem zero_product_card (G : ℤ[X][X]) (hne : G ≠ 0)
    (hgeom : GeometricFactorSwap.Geometric G) (hx : 0 < degreeX G) (hy : 0 < degreeY G)
    (S : Finset Point)
    (hprim : ∀ z ∈ S, (z.1 0).natAbs.Coprime (z.1 1).natAbs ∧
      (z.2 0).natAbs.Coprime (z.2 1).natAbs)
    (hcurve : ∀ z ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1
      (IntegerFactorProjectiveCurve.projective G) = 0)
    (hzero : ∀ z ∈ S, SmoothResidueClasses.badInteger G z = 0) :
    S.card ≤ 4 * (degreeY G + 1) + 4 * (degreeX G + 1) + 8 * degreeX G * degreeY G ^ 2 := by
  classical
  let A := S.filter (fun z ↦ z.1 1 = 0)
  let B := S.filter (fun z ↦ z.2 1 = 0)
  let C := S.filter (fun z ↦ z.1 1 ≠ 0 ∧ z.2 1 ≠ 0)
  have hA := first_axis_card G hne hgeom hy A
    (fun z hz ↦ hprim z (mem_filter.mp hz).1) (fun z hz ↦ hcurve z (mem_filter.mp hz).1)
    (fun _ hz ↦ (mem_filter.mp hz).2)
  have hB := second_axis_card G hne hgeom hx B
    (fun z hz ↦ hprim z (mem_filter.mp hz).1) (fun z hz ↦ hcurve z (mem_filter.mp hz).1)
    (fun _ hz ↦ (mem_filter.mp hz).2)
  have hC := critical_card G hne hgeom hy C
    (fun z hz ↦ hprim z (mem_filter.mp hz).1) (fun z hz ↦ hcurve z (mem_filter.mp hz).1)
    (fun _ hz ↦ (mem_filter.mp hz).2) (by
      intro z hz
      have he := hzero z (mem_filter.mp hz).1
      have hd := (mem_filter.mp hz).2
      exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero hd.1 hd.2))
  have hsub : S ⊆ (A ∪ B) ∪ C := by
    intro z hz
    by_cases ha : z.1 1 = 0
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hz, ha⟩))
    by_cases hb : z.2 1 = 0
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hz, hb⟩))
    · exact mem_union_right _ (mem_filter.mpr ⟨hz, ha, hb⟩)
  calc
    _ ≤ ((A ∪ B) ∪ C).card := card_le_card hsub
    _ ≤ (A ∪ B).card + C.card := card_union_le _ _
    _ ≤ A.card + B.card + C.card := Nat.add_le_add_right (card_union_le _ _) _
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add hA hB) hC

def exceptional (G : ℤ[X][X]) (S : Finset Point) : Finset Point :=
  S.filter (fun z ↦ SmoothResidueClasses.badInteger G z = 0)

theorem exceptional_card (G : ℤ[X][X]) (hne : G ≠ 0)
    (hgeom : GeometricFactorSwap.Geometric G) (hx : 0 < degreeX G) (hy : 0 < degreeY G)
    (S : Finset Point)
    (hprim : ∀ z ∈ S, (z.1 0).natAbs.Coprime (z.1 1).natAbs ∧
      (z.2 0).natAbs.Coprime (z.2 1).natAbs)
    (hcurve : ∀ z ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1
      (IntegerFactorProjectiveCurve.projective G) = 0) :
    (exceptional G S).card ≤
      4 * (degreeY G + 1) + 4 * (degreeX G + 1) + 8 * degreeX G * degreeY G ^ 2 := by
  apply zero_product_card G hne hgeom hx hy (exceptional G S)
    (fun z hz ↦ hprim z (mem_filter.mp hz).1) (fun z hz ↦ hcurve z (mem_filter.mp hz).1)
    (fun _ hz ↦ (mem_filter.mp hz).2)

end PaperP1.ProjectivePrimeExceptions
