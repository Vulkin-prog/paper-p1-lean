module

public import PaperP1.Geometry.OrdinarySourcePolynomialProjection
public import PaperP1.Algebra.GradedPolynomialPresentation

/-! # The actual ordinary image prime of a source curve recovers exactly the original source prime -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceCurveOrdinaryImagePrime

open MvPolynomial HomogeneousSplitRadicalRelations HomogeneousSplitRadicalVeronese SourceVeroneseGrading

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F ι : Type*} [Field F] (c : ι → F) (D : ℕ) (hD : 0 < D) (I J : ι → Finset ℤ)
  (P : Ideal (veronese c D I J))

def evaluation : WeightedPolynomial F ι →ₐ[F] (veronese c D I J ⧸ P) :=
  aeval (fun i ↦ Ideal.Quotient.mk P (OrdinarySourcePolynomialProjection.coordinate c D hD I J i))

def ideal : Ideal (WeightedPolynomial F ι) := RingHom.ker (evaluation c D hD I J P)

theorem evaluation_comp : evaluation c D hD I J P =
    (Ideal.Quotient.mkₐ F P).comp (OrdinarySourcePolynomialProjection.evaluation c D hD I J) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [evaluation, AlgHom.comp_apply, aeval_X, OrdinarySourcePolynomialProjection.evaluation]
  rfl

theorem prime [P.IsPrime] : (ideal c D hD I J P).IsPrime := RingHom.ker_isPrime _

theorem homogeneous (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
    (hP : letI := sourceGrading c D I J hdeg hD; P.IsHomogeneous (sourcePiece c D I J)) :
    (ideal c D hD I J P).IsHomogeneous (homogeneousSubmodule (Fin 3 ⊕ ι) F) := by
  let := sourceGrading c D I J hdeg hD
  let := HomogeneousQuotientGrading.grading (sourcePiece c D I J) P hP
  let G := HomogeneousQuotientGrading.piece (sourcePiece c D I J) P
  let g (i : Fin 3 ⊕ ι) := Ideal.Quotient.mk P (OrdinarySourcePolynomialProjection.coordinate c D hD I J i)
  have hg (i : Fin 3 ⊕ ι) : g i ∈ G 1 :=
    Submodule.mem_map.mpr ⟨_, OrdinarySourcePolynomialProjection.coordinate_mem c D hD I J i, rfl⟩
  exact GradedPolynomialPresentation.kernel_homogeneous G g hg

theorem relations (hmin : ∀ i, 2 ≤ (I i).card + (J i).card)
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) :
    ∀ i, WeightedOrdinarySubstitution.ordinaryRelation (c i) (I i) (J i) i ∈ ideal c D hD I J P := by
  intro i
  change evaluation c D hD I J P _ = 0
  rw [evaluation_comp, AlgHom.comp_apply,
    OrdinarySourcePolynomialProjection.ordinary_relation_zero c D hD I J i (hmin i) (hdeg i), map_zero]

theorem chart_not_mem (hz : OrdinaryCurveSourcePoint.sourceZ c D I J ∉ P) :
    X (Sum.inl (2 : Fin 3)) ∉ ideal c D hD I J P := by
  intro hh
  change evaluation c D hD I J P (X (Sum.inl (2 : Fin 3))) = 0 at hh
  rw [evaluation, aeval_X, OrdinarySourcePolynomialProjection.coordinate_Z] at hh
  exact hz (Ideal.Quotient.eq_zero_iff_mem.mp hh)

theorem sourceIdeal_eq (hmin : ∀ i, 2 ≤ (I i).card + (J i).card)
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
    (hP : letI := sourceGrading c D I J hdeg hD; P.IsHomogeneous (sourcePiece c D I J)) [P.IsPrime]
    (hz : OrdinaryCurveSourcePoint.sourceZ c D I J ∉ P) :
    OrdinaryCurveSourceMap.sourceIdeal c D I J hD hmin hdeg (ideal c D hD I J P)
      (relations c D hD I J P hmin hdeg) (homogeneous c D hD I J P hdeg hP) = P := by
  let := sourceGrading c D I J hdeg hD
  let Q := ideal c D hD I J P
  have hrel := relations c D hD I J P hmin hdeg
  have hQ := homogeneous c D hD I J P hdeg hP
  let S := OrdinaryCurveSourceMap.sourceIdeal c D I J hD hmin hdeg Q hrel hQ
  have hS := OrdinaryCurveSourceMap.sourceIdeal_homogeneous c D I J hD hmin hdeg Q hrel hQ
  change S = P
  have he : (⟨S, hS⟩ : HomogeneousIdeal (sourcePiece c D I J)) = ⟨P, hP⟩ := by
    apply HomogeneousIdeal.ext'
    intro n a ha
    change a ∈ S ↔ a ∈ P
    have haraw : a.val ∈ HomogeneousSplitRadicalGrading.piece c D I J (n * D) := ha
    obtain ⟨p, hp, hpa⟩ := Submodule.mem_map.mp haraw
    change Ideal.Quotient.mk (relationIdeal c D I J) p = a.val at hpa
    have hOrd : a ∈ S ↔ WeightedOrdinarySubstitution.map D p ∈ Q := by
      change (OrdinaryCurveSourceMap.veroneseMap c D I J hD hmin hdeg Q hrel hQ a = 0) ↔ _
      rw [Subtype.ext_iff, OrdinaryCurveSourceMap.veroneseMap_val, ← hpa,
        OrdinaryCurveSourceMap.coordinateMap_mk]
      change Ideal.Quotient.mk Q (WeightedOrdinarySubstitution.map D p) = 0 ↔ _
      exact Ideal.Quotient.eq_zero_iff_mem
    rw [hOrd]
    change evaluation c D hD I J P (WeightedOrdinarySubstitution.map D p) = 0 ↔ a ∈ P
    rw [evaluation_comp, AlgHom.comp_apply,
      OrdinarySourcePolynomialProjection.evaluation_substitution c D hD I J n a p hp hpa,
      map_mul, map_pow]
    change Ideal.Quotient.mk P (OrdinaryCurveSourcePoint.sourceZ c D I J ^ ((D - 1) * n) * a) = 0 ↔ a ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro hh
      exact (Ideal.IsPrime.mem_or_mem inferInstance hh).resolve_left
        (fun hm ↦ hz (Ideal.IsPrime.mem_of_pow_mem inferInstance ((D - 1) * n) hm))
    · intro haP
      exact P.mul_mem_left _ haP
  exact congrArg HomogeneousIdeal.toIdeal he

end PaperP1.SourceCurveOrdinaryImagePrime
