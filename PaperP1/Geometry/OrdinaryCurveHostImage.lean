module

public import PaperP1.Geometry.OrdinaryCurveSourceMap
public import PaperP1.Algebra.HomogeneousAffineLineClassification
public import PaperP1.Algebra.SourceCurveQuotient

/-! # An actual ordinary affine curve point supplies the actual source image host containment -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryCurveHostImage

open Polynomial PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.OrdinaryCurveSourceMap PaperP1.HomogeneousAffineLineClassification

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F : Type*} [Field F]

theorem base_evaluation {ι : Type*} (ρ : WeightedPolynomial F ι →ₐ[F] F) (x y : F)
    (hX : ρ (MvPolynomial.X (Sum.inl (1 : Fin 3))) = x)
    (hY : ρ (MvPolynomial.X (Sum.inl (0 : Fin 3))) = y)
    (hZ : ρ (MvPolynomial.X (Sum.inl (2 : Fin 3))) = 1) (p : MvPolynomial (Fin 3) F) :
    ρ (MvPolynomial.rename Sum.inl p) = AffineLineClassification.valueMap x y (NativeAffineChart.specialization F p) := by
  have heq : ρ.toRingHom.comp (MvPolynomial.rename Sum.inl).toRingHom =
      (AffineLineClassification.valueMap x y).comp (NativeAffineChart.specialization F) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change ρ (MvPolynomial.rename Sum.inl (MvPolynomial.C a)) =
        AffineLineClassification.valueMap x y (NativeAffineChart.specialization F (MvPolynomial.C a))
      rw [MvPolynomial.rename_C, specialization_C]
      have hc : ρ (MvPolynomial.C a) = a := by simp
      simpa only [AffineLineClassification.valueMap, coe_eval₂RingHom, eval₂_C, coe_evalRingHom, eval_C] using hc
    · intro i
      change ρ (MvPolynomial.rename Sum.inl (MvPolynomial.X i)) =
        AffineLineClassification.valueMap x y (NativeAffineChart.specialization F (MvPolynomial.X i))
      rw [MvPolynomial.rename_X]
      fin_cases i <;> simp [specialization_X, specialization_Y, NativeVeroneseAffineIdeal.specialization_Z,
        AffineLineClassification.valueMap, hX, hY, hZ]
  exact RingHom.congr_fun heq p

local instance polynomialRing : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing : CommRing (MvPolynomial (Fin 3) F) := inferInstance

variable (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hD : 0 < D) (hmin : ∀ i, 2 ≤ (I i).card + (J i).card)
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  (Q : Ideal (WeightedPolynomial F (Fin s.length)))
  (hrel : ∀ i, WeightedOrdinarySubstitution.ordinaryRelation (c i) (I i) (J i) i ∈ Q)
  (hQ : Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3 ⊕ Fin s.length) F))

theorem host_image (ρ : WeightedPolynomial F (Fin s.length) →ₐ[F] F) (x y : F)
    (hX : ρ (MvPolynomial.X (Sum.inl (1 : Fin 3))) = x)
    (hY : ρ (MvPolynomial.X (Sum.inl (0 : Fin 3))) = y)
    (hZ : ρ (MvPolynomial.X (Sum.inl (2 : Fin 3))) = 1) (hpoint : Q ≤ RingHom.ker ρ.toRingHom) :
    NativeVeroneseAffineIdeal.affineIdeal F D
      (SourceCurveQuotient.baseIdeal s c D I J hs hD (sourceIdeal c D I J hD hmin hdeg Q hrel hQ)) ≤
      RingHom.ker (AffineLineClassification.valueMap x y) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro a ha
  have hm : SourceVeroneseGradedBaseMap.gradedBaseMap s c D hD I J hs a ∈
      sourceIdeal c D I J hD hmin hdeg Q hrel hQ := ha
  have hz : veroneseMap c D I J hD hmin hdeg Q hrel hQ
      (SourceVeroneseGradedBaseMap.gradedBaseMap s c D hD I J hs a) = 0 := RingHom.mem_ker.mp hm
  have hv := congrArg (fun z : OrdinaryVeronese Q D ↦ (z : OrdinaryRing Q)) hz
  change coordinateMap c D I J hD hmin hdeg Q hrel
    (HomogeneousSplitRadicalBaseInjection.basePolynomialMap c D I J (a : MvPolynomial (Fin 3) F)) = 0 at hv
  change coordinateMap c D I J hD hmin hdeg Q hrel
    (Ideal.Quotient.mk _ (MvPolynomial.rename Sum.inl (a : MvPolynomial (Fin 3) F))) = 0 at hv
  rw [coordinateMap_mk, WeightedOrdinarySubstitution.map_rename] at hv
  have hρ := RingHom.mem_ker.mp (hpoint (Ideal.Quotient.eq_zero_iff_mem.mp hv))
  exact (base_evaluation ρ x y hX hY hZ (a : MvPolynomial (Fin 3) F)).symm.trans hρ

end PaperP1.OrdinaryCurveHostImage
