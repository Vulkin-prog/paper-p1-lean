module

public import PaperP1.Arithmetic.SmallHeightAssociatedPlanePresentation
public import PaperP1.Algebra.BoundedPlaneShear
public import PaperP1.Algebra.IntegerPlaneShear
public import PaperP1.Algebra.RationalizedCriticalPointBound

/-! # An explicit degree-uniform height budget after an actual bounded shear

The original coefficients remain unrestricted. Interpolation is applied after
the original point population is sheared, avoiding a shear coefficient budget.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DegreeUniformPlanePresentation

open Polynomial Finset TotalDegreeMonomials
open RationalBivariateIrreducibility GeometricFactorSwap PolynomialScalarProjection

theorem index_card_le (D : ℕ) : Fintype.card (Index D) ≤ (D + 1) ^ 2 := by
  have hc := Fintype.card_le_of_injective (fun i : Index D ↦ i.val) Subtype.val_injective
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using hc

theorem interpolation_height_bound (D N B : ℕ) (hD : 2 ≤ D) (hDN : D ≤ N)
    (hB : B ≤ (D + 1) * N) :
    BoundedPlaneInterpolation.heightBound D B ≤ N ^ (32 * D ^ 3) := by
  let r := Fintype.card (Index D)
  have hN : 2 ≤ N := hD.trans hDN
  have hNplus : N + 1 ≤ N ^ 2 := by
    have hm : N * 2 ≤ N * N := Nat.mul_le_mul_left N hN
    nlinarith
  have hDplus : D + 1 ≤ N ^ 2 := by omega
  have hB3 : B ≤ N ^ 3 := by
    calc
      _ ≤ (D + 1) * N := hB
      _ ≤ N ^ 2 * N := Nat.mul_le_mul_right N hDplus
      _ = _ := by ring
  have hr4 : r ≤ N ^ 4 := by
    calc
      _ ≤ (D + 1) ^ 2 := index_card_le D
      _ ≤ (N ^ 2) ^ 2 := Nat.pow_le_pow_left hDplus 2
      _ = _ := by ring
  have hrD : r ≤ 4 * D ^ 2 := by
    calc
      _ ≤ (D + 1) ^ 2 := index_card_le D
      _ ≤ (2 * D) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = _ := by ring
  have h6 : 6 ≤ N ^ 3 := by
    calc
      _ ≤ 2 ^ 3 := by decide
      _ ≤ _ := Nat.pow_le_pow_left hN 3
  have hcoef : 6 * r ≤ N ^ 7 := by
    calc
      _ ≤ 6 * N ^ 4 := Nat.mul_le_mul_left _ hr4
      _ ≤ N ^ 3 * N ^ 4 := Nat.mul_le_mul_right _ h6
      _ = _ := by ring
  have hpow : B ^ D ≤ N ^ (3 * D) := by
    calc
      _ ≤ (N ^ 3) ^ D := Nat.pow_le_pow_left hB3 D
      _ = _ := (pow_mul _ _ _).symm
  have hone : 1 ≤ N ^ (3 * D) := Nat.one_le_pow _ _ (by omega)
  have hbase : 3 * r * (B ^ D + 1) ≤ N ^ (3 * D + 7) := by
    calc
      _ ≤ 3 * r * (2 * N ^ (3 * D)) := Nat.mul_le_mul_left _ (by omega)
      _ = 6 * r * N ^ (3 * D) := by ring
      _ ≤ N ^ 7 * N ^ (3 * D) := Nat.mul_le_mul_right _ hcoef
      _ = _ := by rw [← pow_add]; congr 1; omega
  have he : (3 * D + 7) * (r - 1) ≤ 32 * D ^ 3 := by
    calc
      _ ≤ (3 * D + 7) * (4 * D ^ 2) :=
        Nat.mul_le_mul_left _ ((Nat.sub_le r 1).trans hrD)
      _ ≤ (8 * D) * (4 * D ^ 2) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  change (3 * r * (B ^ D + 1)) ^ (r - 1) ≤ _
  calc
    _ ≤ (N ^ (3 * D + 7)) ^ (r - 1) := Nat.pow_le_pow_left hbase _
    _ = N ^ ((3 * D + 7) * (r - 1)) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) he

theorem point_natAbs_bounds (D t : ℕ) (ht : t ≤ D) (N : ℕ) (z : ℤ × ℤ)
    (hx : z.1.natAbs ≤ N) (hy : z.2.natAbs ≤ N) :
    (IntegerPlaneShear.point (t : ℤ) z).1.natAbs ≤ (D + 1) * N ∧
      (IntegerPlaneShear.point (t : ℤ) z).2.natAbs ≤ (D + 1) * N := by
  change (z.1 - (t : ℤ) * z.2).natAbs ≤ (D + 1) * N ∧ z.2.natAbs ≤ (D + 1) * N
  have hh := Int.natAbs_sub_le z.1 ((t : ℤ) * z.2)
  rw [Int.natAbs_mul, Int.natAbs_natCast] at hh
  constructor
  · calc
      _ ≤ z.1.natAbs + t * z.2.natAbs := hh
      _ ≤ N + D * N := Nat.add_le_add hx (Nat.mul_le_mul ht hy)
      _ = _ := by ring
  · exact hy.trans (Nat.le_mul_of_pos_left N (by omega : 0 < D + 1))

theorem exists_presentation (P : ℤ[X][X]) (D N : ℕ) (hD : 2 ≤ D) (hDN : D ≤ N)
    (hdegree : PlaneCurvePointCount.degree P = D) (hgeo : Geometric P)
    (S : Finset (ℤ × ℤ))
    (hS : ∀ z ∈ S, P.evalEval z.1 z.2 = 0 ∧ z.1.natAbs ≤ N ∧ z.2.natAbs ≤ N)
    (hmany : D ^ 2 < S.card) :
    ∃ t : ℕ, t ≤ D ∧ ∃ Q : ℤ[X][X], PlaneCurvePointCount.degree Q = D ∧
      Q.natDegree = D ∧ Geometric Q ∧ BivariateHeight.height Q ≤ N ^ (32 * D ^ 3) ∧
      Associated (rationalize (BivariateLinearShear.shear (t : ℤ) P)) (rationalize Q) ∧
      ∀ z ∈ S, Q.evalEval (IntegerPlaneShear.point (t : ℤ) z).1
        (IntegerPlaneShear.point (t : ℤ) z).2 = 0 := by
  classical
  have hne : P ≠ 0 := by
    intro hz
    have hh : PlaneCurvePointCount.degree P = 0 := by simp [PlaneCurvePointCount.degree, hz]
    omega
  obtain ⟨t, ht, hout⟩ := BoundedPlaneShear.exists_full_outer_degree P hne
  rw [hdegree] at ht hout
  let R := BivariateLinearShear.shear (t : ℤ) P
  have hRdegree : PlaneCurvePointCount.degree R = D :=
    (BivariateLinearShear.shear_degree (t : ℤ) P).trans hdegree
  have hRgeo : Geometric R := IntegerPlaneShear.geometric (t : ℤ) P hne hgeo
  have hRne : R ≠ 0 := by
    intro hz
    have hh : PlaneCurvePointCount.degree R = 0 := by simp [PlaneCurvePointCount.degree, hz]
    omega
  have hRF : Irreducible (rationalize R) :=
    ScalarIrreducibilityReflection.geometric_rational_irreducible R hRne hRgeo
  have hAbs : Irreducible (extend (rationalize R) : ℂ[X][X]) := by
    rw [ComplexProjectiveIrreducibility.rational_extension]
    exact (HomogenizationIrreducibilityReflection.geometric_iff_affine R hRne).mp hRgeo
  let H := (D + 1) * N
  let U := S.image (IntegerPlaneShear.point (t : ℤ))
  have hHpos : 0 < H := Nat.mul_pos (by omega) (by omega)
  have hUcard : U.card = S.card := card_image_of_injective _ (IntegerPlaneShear.point_injective (t : ℤ))
  have hbox : ∀ z ∈ U, z.1.natAbs ≤ H ∧ z.2.natAbs ≤ H := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
    exact point_natAbs_bounds D t ht N z (hS z hz).2.1 (hS z hz).2.2
  have hzero : ∀ z ∈ U, R.evalEval z.1 z.2 = 0 := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
    exact IntegerPlaneShear.point_zero (t : ℤ) P z (hS z hz).1
  obtain ⟨Q, hQ, hQabs, hassoc, hQdegree, hheight, hQzero⟩ :=
    SmallHeightAssociatedPlanePresentation.exists_presentation R hRF hAbs H (by omega) U hbox hzero
      (by rw [hRdegree, hUcard]; exact hmany)
  have hQne : Q ≠ 0 := by
    intro hz
    apply hQ.ne_zero
    simp only [rationalize, hz, Polynomial.map_zero]
  have hQgeo : Geometric Q :=
    (HomogenizationIrreducibilityReflection.geometric_iff_affine Q hQne).mpr (by
      rw [← ComplexProjectiveIrreducibility.rational_extension]
      exact hQabs)
  have houter₁ := Polynomial.natDegree_le_of_dvd hassoc.dvd hQ.ne_zero
  have houter₂ := Polynomial.natDegree_le_of_dvd hassoc.symm.dvd hRF.ne_zero
  rw [RationalizedCriticalPointBound.outer_degree, RationalizedCriticalPointBound.outer_degree] at houter₁ houter₂
  have houter : Q.natDegree = D := by
    have hh := Nat.le_antisymm houter₂ houter₁
    change Q.natDegree = R.natDegree at hh
    exact hh.trans hout
  have hheight' : BivariateHeight.height Q ≤ BoundedPlaneInterpolation.heightBound D H := by
    simpa only [hRdegree] using hheight
  refine ⟨t, ht, Q, hQdegree.trans hRdegree, houter, hQgeo,
    hheight'.trans (interpolation_height_bound D N H hD hDN le_rfl), hassoc, ?_⟩
  intro z hz
  exact hQzero _ (mem_image_of_mem _ hz)

end PaperP1.DegreeUniformPlanePresentation
