module

public import PaperP1.Geometry.ProjChartFunctionFieldNaturality
public import PaperP1.Algebra.GradedDehomogenization

/-! # Naturality of actual dehomogenized elements in the projective function fields -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.ProjChartDehomogenizationNaturality

open AlgebraicGeometry HomogeneousLocalization

variable {A σ B τ : Type u} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {G : ℕ → σ} {H : ℕ → τ} [GradedRing G] [GradedRing H]
  (f : G →+*ᵍ H)
  (hf : (HomogeneousIdeal.irrelevant H).toIdeal ≤
    ((HomogeneousIdeal.irrelevant G).toIdeal.map f.toRingHom).radical)
  (hG : (HomogeneousIdeal.irrelevant G).toIdeal ≠ ⊥)
  (hH : (HomogeneousIdeal.irrelevant H).toIdeal ≠ ⊥) (hinj : Function.Injective f)

theorem dehomogenization_natural {b : A} (hb : b ∈ G 1) (hb0 : b ≠ 0) (hfb0 : f b ≠ 0) (x : A) :
    letI := ProjIntegral.integral G hG
    letI := ProjIntegral.integral H hH
    ProjFunctionFieldMap.map f hf hG hH hinj
        (ProjChartFunctionField.chartMap G hG hb0 (GradedDehomogenization.map G hb x)) =
      ProjChartFunctionField.chartMap H hH hfb0
        (GradedDehomogenization.map H (f.map_mem hb) (f x)) := by
  let := ProjIntegral.integral G hG
  let := ProjIntegral.integral H hH
  exact (DFunLike.congr_fun
    (ProjChartFunctionFieldNaturality.chartMap_natural f hf hG hH hinj hb hb0 hfb0)
      (GradedDehomogenization.map G hb x)).trans
        (congrArg (ProjChartFunctionField.chartMap H hH hfb0)
          (DFunLike.congr_fun (GradedDehomogenization.map_natural G hb f) x))

variable (G) in
theorem chart_dehomogenization_congr {b₁ b₂ : A} (hb₁ : b₁ ∈ G 1) (hb₂ : b₂ ∈ G 1)
    (hb₁0 : b₁ ≠ 0) (hb₂0 : b₂ ≠ 0) (h : b₁ = b₂) (x : A) :
    letI := ProjIntegral.integral G hG
    ProjChartFunctionField.chartMap G hG hb₁0 (GradedDehomogenization.map G hb₁ x) =
      ProjChartFunctionField.chartMap G hG hb₂0 (GradedDehomogenization.map G hb₂ x) := by
  subst b₂
  rfl

end PaperP1.ProjChartDehomogenizationNaturality
