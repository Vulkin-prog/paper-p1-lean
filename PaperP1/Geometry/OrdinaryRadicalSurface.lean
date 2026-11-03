module

public import PaperP1.Geometry.OrdinaryCurveSourceMap
public import PaperP1.Algebra.WeightedOrdinaryAffineIdeal
public import PaperP1.Algebra.AffineQuotientChartComparison
public import PaperP1.Algebra.HomogeneousChartCoordinateChange

/-! # The actual ordinary radical surface has the same affine chart as the actual weighted source -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryRadicalSurface

open MvPolynomial HomogeneousLocalization PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.WeightedOrdinaryAffineIdeal PaperP1.OrdinaryCurveSourceMap

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F ι : Type*} [Field F] (c : ι → F) (I J : ι → Finset ℤ)

theorem relation_mem (i : ι) : WeightedOrdinarySubstitution.ordinaryRelation (c i) (I i) (J i) i ∈
    ordinaryIdeal c I J := Ideal.subset_span (Set.mem_range_self i)

theorem homogeneous (hmin : ∀ i, 2 ≤ (I i).card + (J i).card) :
    (ordinaryIdeal c I J).IsHomogeneous (homogeneousSubmodule (Fin 3 ⊕ ι) F) := by
  apply Ideal.homogeneous_span
  rintro _ ⟨i, rfl⟩
  exact ⟨_, WeightedOrdinarySubstitution.ordinaryRelation_homogeneous (c i) (I i) (J i) i (hmin i)⟩

@[instance_reducible] def grading (hmin : ∀ i, 2 ≤ (I i).card + (J i).card) :
    GradedAlgebra (ordinaryPiece (ordinaryIdeal c I J)) :=
  HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin 3 ⊕ ι) F) (ordinaryIdeal c I J)
    (homogeneous c I J hmin)

variable (D : ℕ) (hD : 0 < D) (hmin : ∀ i, 2 ≤ (I i).card + (J i).card)
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)

local instance sourceRing : CommRing (HomogeneousSplitRadicalGrading.CoordinateRing c D I J) := inferInstance
local instance targetRing : CommRing (OrdinaryRing (ordinaryIdeal c I J)) := inferInstance

theorem chart_bijective :
    letI := HomogeneousSplitRadicalGrading.grading c D I J hdeg
    letI := grading c I J hmin
    Function.Bijective (Away.map
      (gradedCoordinateMap c D I J hD hmin hdeg (ordinaryIdeal c I J) (relation_mem c I J))
      (Ideal.Quotient.mk (relationIdeal c D I J) (X (Sum.inl (2 : Fin 3))))) := by
  let := HomogeneousSplitRadicalGrading.grading c D I J hdeg
  let := grading c I J hmin
  let M := ordinaryIdeal c I J
  let f := gradedCoordinateMap c D I J hD hmin hdeg M (relation_mem c I J)
  let b := Ideal.Quotient.mk (relationIdeal c D I J) (X (Sum.inl (2 : Fin 3)))
  let z := Ideal.Quotient.mk M (X (Sum.inl (2 : Fin 3)))
  have hb : b ∈ HomogeneousSplitRadicalGrading.piece c D I J 1 :=
    HomogeneousSplitRadicalGrading.base_variable_mem c D I J 2
  have hz : z ∈ ordinaryPiece M 1 := Submodule.mem_map.mpr ⟨_, isHomogeneous_X F _, rfl⟩
  have hfb : f b = z := by
    change coordinateMap c D I J hD hmin hdeg M (relation_mem c I J)
      (Ideal.Quotient.mk _ (X (Sum.inl (2 : Fin 3)))) = _
    rw [coordinateMap_mk, WeightedOrdinarySubstitution.map_base]
  let e := AffineQuotientChartComparison.chartEquiv (X (Sum.inl (2 : Fin 3)))
    (relationIdeal c D I J) M (HomogeneousSplitRadicalGrading.piece c D I J) (ordinaryPiece M)
    hb hz (ideals_sup_chart c D I J)
  let C := HomogeneousChartCoordinateChange.equiv (ordinaryPiece M) hfb
  have he (p : WeightedPolynomial F ι) :
      e (GradedDehomogenization.map (HomogeneousSplitRadicalGrading.piece c D I J) hb
        (Ideal.Quotient.mk _ p)) = GradedDehomogenization.map (ordinaryPiece M) hz (Ideal.Quotient.mk M p) :=
    AffineQuotientChartComparison.chartEquiv_dehomogenization _ _ _ _ _ hb hz (ideals_sup_chart c D I J) p
  have hc (x : HomogeneousSplitRadicalGrading.CoordinateRing c D I J) :
      C (Away.map f b (GradedDehomogenization.map (HomogeneousSplitRadicalGrading.piece c D I J) hb x)) =
        e (GradedDehomogenization.map (HomogeneousSplitRadicalGrading.piece c D I J) hb x) := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hn := DFunLike.congr_fun (GradedDehomogenization.map_natural
      (HomogeneousSplitRadicalGrading.piece c D I J) hb f)
      (Ideal.Quotient.mk (relationIdeal c D I J) p)
    simp only [RingHom.comp_apply] at hn
    have hC := HomogeneousChartCoordinateChange.equiv_dehomogenization (ordinaryPiece M) hfb
      (f.map_mem hb) hz (f (Ideal.Quotient.mk (relationIdeal c D I J) p))
    refine (congrArg C hn).trans (hC.trans ?_)
    rw [he]
    change GradedDehomogenization.map (ordinaryPiece M) hz
      (coordinateMap c D I J hD hmin hdeg M (relation_mem c I J) (Ideal.Quotient.mk _ p)) = _
    rw [coordinateMap_mk]
    let φ := (GradedDehomogenization.map (ordinaryPiece M) hz).comp (Ideal.Quotient.mk M)
    have hZ : φ (X (Sum.inl (2 : Fin 3))) = 1 :=
      GradedDehomogenizationQuotient.map_variable (ordinaryPiece M) hz
    exact substitution_eq_at_one φ hZ D p
  have hall (u : Away (HomogeneousSplitRadicalGrading.piece c D I J) b) : C (Away.map f b u) = e u := by
    obtain ⟨x, rfl⟩ := GradedDehomogenization.map_surjective (HomogeneousSplitRadicalGrading.piece c D I J) hb u
    exact hc x
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply e.injective
    rw [← hall x, ← hall y, hxy]
  · intro y
    obtain ⟨x, hx⟩ := e.surjective (C y)
    exact ⟨x, C.injective ((hall x).trans hx)⟩

end PaperP1.OrdinaryRadicalSurface
