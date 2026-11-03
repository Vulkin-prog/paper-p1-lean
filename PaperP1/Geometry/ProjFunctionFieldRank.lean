module

public import PaperP1.Geometry.ProjFunctionFieldDegree
public import PaperP1.Algebra.GradedDehomogenizationRank

/-! # Actual projective function-field degree equals the finite graded module rank -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u v

namespace PaperP1.ProjFunctionFieldRank

open AlgebraicGeometry HomogeneousLocalization

section Charts

variable {A B σ τ : Type u} [CommRing A] [IsDomain A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [IsDomain B] [SetLike τ B] [AddSubgroupClass τ B]
  {G : ℕ → σ} {H : ℕ → τ} [GradedRing G] [GradedRing H]
  (f : G →+*ᵍ H)
  (hf : (HomogeneousIdeal.irrelevant H).toIdeal ≤
    ((HomogeneousIdeal.irrelevant G).toIdeal.map f.toRingHom).radical)
  (hG : (HomogeneousIdeal.irrelevant G).toIdeal ≠ ⊥)
  (hH : (HomogeneousIdeal.irrelevant H).toIdeal ≠ ⊥) (hinj : Function.Injective f)

set_option backward.isDefEq.respectTransparency false in
theorem finrank_eq_chart {b : A} (hb : b ∈ G 1) (hb0 : b ≠ 0) (hfb0 : f b ≠ 0) :
    letI := ProjIntegral.integral G hG
    letI := ProjIntegral.integral H hH
    letI : Algebra (Proj G).functionField (Proj H).functionField :=
      (ProjFunctionFieldMap.map f hf hG hH hinj).toAlgebra
    letI : Algebra (Away G b) (Away H (f b)) := (Away.map f b).toAlgebra
    Module.finrank (Proj G).functionField (Proj H).functionField =
      Module.finrank (Away G b) (Away H (f b)) := by
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
  exact IsFractionRing.finrank_eq (Away G b) (Proj G).functionField
    (Away H (f b)) (Proj H).functionField

end Charts

section GradedModules

variable {F A B : Type u} {ι : Type v} [Field F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B] [Fintype ι]
  {G : ℕ → Submodule F A} {H : ℕ → Submodule F B}
  [GradedAlgebra G] [GradedAlgebra H] [IsDomain A] [IsDomain B]
  (f : G →+*ᵍ H)
  (hf : (HomogeneousIdeal.irrelevant H).toIdeal ≤
    ((HomogeneousIdeal.irrelevant G).toIdeal.map f.toRingHom).radical)
  (hG : (HomogeneousIdeal.irrelevant G).toIdeal ≠ ⊥)
  (hH : (HomogeneousIdeal.irrelevant H).toIdeal ≠ ⊥) (hinj : Function.Injective f)
  {b : A} (hb : b ∈ G 1) (hb0 : b ≠ 0)
  (v : ι → B) (w : ι → ℕ) (hv : ∀ i, v i ∈ H (w i))

include hb hb0 hv in
theorem finrank_eq_module
    (hgen : letI : Algebra A B := f.toRingHom.toAlgebra
      Submodule.span A (Set.range v) = ⊤) :
    letI : Algebra A B := f.toRingHom.toAlgebra
    letI := ProjIntegral.integral G hG
    letI := ProjIntegral.integral H hH
    letI : Algebra (Proj G).functionField (Proj H).functionField :=
      (ProjFunctionFieldMap.map f hf hG hH hinj).toAlgebra
    Module.finrank (Proj G).functionField (Proj H).functionField = Module.finrank A B := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let := ProjIntegral.integral G hG
  let := ProjIntegral.integral H hH
  let : Algebra (Proj G).functionField (Proj H).functionField :=
    (ProjFunctionFieldMap.map f hf hG hH hinj).toAlgebra
  let : Algebra (Away G b) (Away H (f b)) := (Away.map f b).toAlgebra
  have hfb0 : f b ≠ 0 := fun h ↦ hb0 (hinj (h.trans (map_zero f).symm))
  exact (finrank_eq_chart f hf hG hH hinj hb hb0 hfb0).trans
    (GradedDehomogenizationRank.finrank_eq f hb hb0 hinj v w hv hgen)

end GradedModules

end PaperP1.ProjFunctionFieldRank
