module

public import PaperP1.Geometry.ProjChartFunctionFieldNaturality
public import PaperP1.Algebra.GradedChartBasis
public import Mathlib.LinearAlgebra.Dimension.Localization

/-! # The numerical degree of the actual scheme function-field map from a free chart basis -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u v

namespace PaperP1.ProjFunctionFieldDegree

open AlgebraicGeometry CategoryTheory HomogeneousLocalization Module

variable {A B σ τ : Type u} [CommRing A] [IsDomain A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [IsDomain B] [SetLike τ B] [AddSubgroupClass τ B]
  {G : ℕ → σ} {H : ℕ → τ} [GradedRing G] [GradedRing H]
  (f : G →+*ᵍ H)
  (hf : (HomogeneousIdeal.irrelevant H).toIdeal ≤
    ((HomogeneousIdeal.irrelevant G).toIdeal.map f.toRingHom).radical)
  (hG : (HomogeneousIdeal.irrelevant G).toIdeal ≠ ⊥)
  (hH : (HomogeneousIdeal.irrelevant H).toIdeal ≠ ⊥) (hinj : Function.Injective f)

set_option backward.isDefEq.respectTransparency false in
theorem finrank_eq_chart {b : A} (hb : b ∈ G 1) (hb0 : b ≠ 0) (hfb0 : f b ≠ 0)
    {ι : Type v} [Fintype ι]
    (e : letI : Algebra (Away G b) (Away H (f b)) := (Away.map f b).toAlgebra;
      Basis ι (Away G b) (Away H (f b))) :
    letI := ProjIntegral.integral G hG
    letI := ProjIntegral.integral H hH
    letI : Algebra (Proj G).functionField (Proj H).functionField :=
      (ProjFunctionFieldMap.map f hf hG hH hinj).toAlgebra
    Module.finrank (Proj G).functionField (Proj H).functionField = Fintype.card ι := by
  let := ProjIntegral.integral G hG
  let := ProjIntegral.integral H hH
  let : Algebra (Away G b) (Away H (f b)) := (Away.map f b).toAlgebra
  let : Algebra (Proj G).functionField (Proj H).functionField :=
    (ProjFunctionFieldMap.map f hf hG hH hinj).toAlgebra
  let : Algebra (Away G b) (Proj G).functionField :=
    (ProjChartFunctionField.chartMap G hG hb0).toAlgebra
  let : Algebra (Away H (f b)) (Proj H).functionField :=
    (ProjChartFunctionField.chartMap H hH hfb0).toAlgebra
  let : Algebra (Away G b) (Proj H).functionField :=
    ((ProjFunctionFieldMap.map f hf hG hH hinj).comp
      (ProjChartFunctionField.chartMap G hG hb0)).toAlgebra
  have : IsScalarTower (Away G b) (Proj G).functionField (Proj H).functionField :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have : IsScalarTower (Away G b) (Away H (f b)) (Proj H).functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    exact DFunLike.congr_fun
      (ProjChartFunctionFieldNaturality.chartMap_natural f hf hG hH hinj hb hb0 hfb0) a
  have : IsFractionRing (Away G b) (Proj G).functionField :=
    ProjChartFunctionField.chart_isFractionRing G hG hb0 hb
  have : IsFractionRing (Away H (f b)) (Proj H).functionField :=
    ProjChartFunctionField.chart_isFractionRing H hH hfb0 (f.map_mem hb)
  have : IsDomain (Away G b) := GradedChartBasis.chart_isDomain G hb0
  calc
    Module.finrank (Proj G).functionField (Proj H).functionField =
        Module.finrank (Away G b) (Away H (f b)) :=
      IsFractionRing.finrank_eq (Away G b) (Proj G).functionField (Away H (f b)) (Proj H).functionField
    _ = Fintype.card ι := Module.finrank_eq_card_basis e

end PaperP1.ProjFunctionFieldDegree
