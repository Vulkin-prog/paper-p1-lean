module

public import PaperP1.Geometry.P3ProjectiveFactorLocus
public import PaperP1.Geometry.P3FactorImageFactorization
public import PaperP1.Algebra.HomogeneousFactorDegrees

/-! # Exact geometric reducibility criterion for the actual finite projective factor locus -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3FactorLocusIrreducibility

open AlgebraicGeometry CategoryTheory MvPolynomial P3HomogeneousCoefficientFamily
open P3ProjectiveFactorLocus
open scoped Classical

variable {F : Type} [Field F]

theorem degree_polynomial {n d : ℕ} (h : n = d) (a : Index n → F) :
    polynomial d (degreeVector h a) = polynomial n a := by
  subst d
  rfl

theorem degree_coefficients {n d : ℕ} (h : n = d) (P : MvPolynomial (Fin 4) F) :
    degreeVector h (fun m : Index n ↦ P.coeff m.val) = fun m : Index d ↦ P.coeff m.val := by
  subst d
  rfl

theorem degree_image_iff {n d : ℕ} (h : n = d) {X : Scheme}
    (g : X ⟶ P3FactorMultiplicationMap.coefficientScheme n) (w : Index d → F) (hw : w ≠ 0) :
    IntegerCoefficientProjectivePoint.point w hw ∈ Set.range (g ≫ degreeMap h) ↔
      IntegerCoefficientProjectivePoint.point (degreeVector h.symm w)
        (degreeVector_ne_zero h.symm w hw) ∈ Set.range g := by
  subst d
  rfl

theorem coefficient_vector_ne_zero (d : ℕ) (P : MvPolynomial (Fin 4) F)
    (hP : P.IsHomogeneous d) (hP0 : P ≠ 0) : (fun m : Index d ↦ P.coeff m.val) ≠ 0 := by
  intro hz
  have he := reconstruct d P hP
  rw [hz] at he
  simp only [polynomial, Pi.zero_apply, monomial_zero, Finset.sum_const_zero] at he
  exact hP0 he.symm

theorem product_coefficients (e f : ℕ) (A B : MvPolynomial (Fin 4) F)
    (hA : A.IsHomogeneous e) (hB : B.IsHomogeneous f) :
    P3FactorSegreFieldPoint.productVector e f (fun m ↦ A.coeff m.val) (fun m ↦ B.coeff m.val) =
      fun m : Index (e + f) ↦ (A * B).coeff m.val := by
  funext m
  rw [P3FactorSegreFieldPoint.productVector_coefficient, reconstruct e A hA, reconstruct f B hB]

theorem factorization_mem (d : ℕ) (e : Partition d) (w : Index d → F) (hw : w ≠ 0)
    (A B : MvPolynomial (Fin 4) F) (hA : A.IsHomogeneous e.val.val)
    (hB : B.IsHomogeneous (d - e.val.val)) (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (hAB : polynomial d w = A * B) : IntegerCoefficientProjectivePoint.point w hw ∈ locus d := by
  have ha := coefficient_vector_ne_zero _ A hA hA0
  have hb := coefficient_vector_ne_zero _ B hB hB0
  have hv : degreeVector (partition_degree d e)
      (P3FactorSegreFieldPoint.productVector _ _ (fun m ↦ A.coeff m.val) (fun m ↦ B.coeff m.val)) = w := by
    rw [product_coefficients _ _ A B hA hB, degree_coefficients, ← hAB]
    exact funext (coeff_index d w)
  have hm := product_point_mem_locus d e (fun m ↦ A.coeff m.val) (fun m ↦ B.coeff m.val) ha hb
  simpa only [hv] using hm

theorem zero_degree_unit (P : MvPolynomial (Fin 4) F) (hP : P ≠ 0) (hd : P.totalDegree = 0) :
    IsUnit P := by
  have he : P = C (P.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp hd
  have hc : P.coeff 0 ≠ 0 := by
    intro hz
    apply hP
    rw [he, hz, map_zero]
  rw [he]
  exact (isUnit_iff_ne_zero.mpr hc).map C

theorem mem_of_not_irreducible (d : ℕ) (hd : 0 < d) (w : Index d → F) (hw : w ≠ 0)
    (hirr : ¬ Irreducible (polynomial d w)) :
    IntegerCoefficientProjectivePoint.point w hw ∈ locus d := by
  have hP0 := nonzero d w hw
  have hP := homogeneous d w
  have hu := P3FactorImageFactorization.positive_homogeneous_not_unit (polynomial d w) hd hP hP0
  have hex : ∃ A B : MvPolynomial (Fin 4) F,
      polynomial d w = A * B ∧ ¬ IsUnit A ∧ ¬ IsUnit B := by
    by_contra hn
    apply hirr
    refine ⟨hu, ?_⟩
    intro A B hAB
    by_contra hunit
    exact hn ⟨A, B, hAB, (not_or.mp hunit).1, (not_or.mp hunit).2⟩
  obtain ⟨A, B, hAB, huA, huB⟩ := hex
  have hAB0 : A * B ≠ 0 := by rw [← hAB]; exact hP0
  have hA0 := left_ne_zero_of_mul hAB0
  have hB0 := right_ne_zero_of_mul hAB0
  have hAd : 0 < A.totalDegree := by
    by_contra hn
    exact huA (zero_degree_unit A hA0 (Nat.eq_zero_of_not_pos hn))
  have hBd : 0 < B.totalDegree := by
    by_contra hn
    exact huB (zero_degree_unit B hB0 (Nat.eq_zero_of_not_pos hn))
  have hsum : A.totalDegree + B.totalDegree = d := by
    rw [← totalDegree_mul_of_isDomain hA0 hB0, ← hAB]
    exact hP.totalDegree hP0
  obtain ⟨hAh, hBh⟩ := HomogeneousFactorDegrees.homogeneous_factors A B hAB0 d (hAB ▸ hP)
  let e : Partition d := ⟨⟨A.totalDegree, by omega⟩, hAd, by change A.totalDegree < d; omega⟩
  apply factorization_mem d e w hw A B hAh _ hA0 hB0 hAB
  have hf : d - A.totalDegree = B.totalDegree := by omega
  change B.IsHomogeneous (d - A.totalDegree)
  rw [hf]
  exact hBh

variable [IsAlgClosed F]

theorem not_irreducible_of_mem (d : ℕ) (w : Index d → F) (hw : w ≠ 0)
    (hm : IntegerCoefficientProjectivePoint.point w hw ∈ locus d) :
    ¬ Irreducible (polynomial d w) := by
  obtain ⟨e, he⟩ := Set.mem_iUnion.mp hm
  have himage : IntegerCoefficientProjectivePoint.point
      (degreeVector (partition_degree d e).symm w)
      (degreeVector_ne_zero _ w hw) ∈
      Set.range (P3FactorMultiplicationMap.multiplication e.val.val (d - e.val.val)) :=
    (degree_image_iff (partition_degree d e) _ w hw).mp he
  have hf : 0 < d - e.val.val := Nat.sub_pos_of_lt e.property.2
  have hn := P3FactorImageFactorization.not_irreducible _ _ e.property.1 hf
    (degreeVector (partition_degree d e).symm w) (degreeVector_ne_zero _ w hw) himage
  rw [degree_polynomial] at hn
  exact hn

theorem mem_iff_not_irreducible (d : ℕ) (hd : 0 < d) (w : Index d → F) (hw : w ≠ 0) :
    IntegerCoefficientProjectivePoint.point w hw ∈ locus d ↔ ¬ Irreducible (polynomial d w) :=
  ⟨not_irreducible_of_mem d w hw, mem_of_not_irreducible d hd w hw⟩

end PaperP1.P3FactorLocusIrreducibility
