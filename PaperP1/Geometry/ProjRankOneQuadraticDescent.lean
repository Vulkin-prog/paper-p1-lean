module

public import PaperP1.Geometry.ProjFunctionFieldRankOne
public import PaperP1.Geometry.ProjChartFunctionFieldTransport

/-! # Literal quadratic equations descend to the actual projective base field at rank one -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u v

namespace PaperP1.ProjRankOneQuadraticDescent

open AlgebraicGeometry HomogeneousLocalization

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

include hf hH hinj hv in
theorem dehomogenized_isSquare
    (hgen : letI : Algebra A B := f.toRingHom.toAlgebra
      Submodule.span A (Set.range v) = ⊤)
    (hr : letI : Algebra A B := f.toRingHom.toAlgebra; Module.finrank A B = 1)
    (a : A) (root : B) (hquad : root ^ 2 = f a) :
    letI := ProjIntegral.integral G hG
    IsSquare (ProjChartFunctionField.chartMap G hG hb0 (GradedDehomogenization.map G hb a)) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let := ProjIntegral.integral G hG
  let := ProjIntegral.integral H hH
  let : Algebra (Proj G).functionField (Proj H).functionField :=
    (ProjFunctionFieldMap.map f hf hG hH hinj).toAlgebra
  have hfield := (ProjFunctionFieldRank.finrank_eq_module f hf hG hH hinj hb hb0 v w hv hgen).trans hr
  apply (RankOneFieldSquares.isSquare_iff hfield _).mp
  have hfb0 : f b ≠ 0 := fun hz ↦ hb0 (hinj (hz.trans (map_zero f).symm))
  refine ⟨ProjChartFunctionField.chartMap H hH hfb0
    (GradedDehomogenization.map H (f.map_mem hb) root), ?_⟩
  change ProjFunctionFieldMap.map f hf hG hH hinj
    (ProjChartFunctionField.chartMap G hG hb0 (GradedDehomogenization.map G hb a)) = _
  have hnat : ProjFunctionFieldMap.map f hf hG hH hinj
      (ProjChartFunctionField.chartMap G hG hb0 (GradedDehomogenization.map G hb a)) =
      ProjChartFunctionField.chartMap H hH hfb0 (Away.map f b (GradedDehomogenization.map G hb a)) :=
    DFunLike.congr_fun (ProjChartFunctionFieldNaturality.chartMap_natural f hf hG hH hinj hb hb0 hfb0)
      (GradedDehomogenization.map G hb a)
  rw [hnat, GradedDehomogenizationModule.natural_apply f hb a]
  rw [← map_mul, ← map_mul, ← pow_two, hquad]

include hf hG hH hinj hb0 hv in
theorem parametrized_isSquare {R : Type u} [CommRing R]
    (hgen : letI : Algebra A B := f.toRingHom.toAlgebra
      Submodule.span A (Set.range v) = ⊤)
    (hr : letI : Algebra A B := f.toRingHom.toAlgebra; Module.finrank A B = 1)
    (a : A) (root : B) (hquad : root ^ 2 = f a) (e : Away G b ≃+* R) :
    IsSquare (algebraMap R (FractionRing R) (e (GradedDehomogenization.map G hb a))) := by
  let := ProjIntegral.integral G hG
  exact (ProjChartFunctionFieldTransport.isSquare_iff G hG hb hb0 e _).mp
    (dehomogenized_isSquare f hf hG hH hinj hb hb0 v w hv hgen hr a root hquad)

end PaperP1.ProjRankOneQuadraticDescent
