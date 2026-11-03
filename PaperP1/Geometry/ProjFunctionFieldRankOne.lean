module

public import PaperP1.Geometry.ProjFunctionFieldRank
public import PaperP1.Algebra.RankOneFieldSquares

/-! # Rank-one finite graded maps give actual projective function-field isomorphisms -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u v

namespace PaperP1.ProjFunctionFieldRankOne

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

def equiv_of_module_rank_one
    (hgen : letI : Algebra A B := f.toRingHom.toAlgebra
      Submodule.span A (Set.range v) = ⊤)
    (hr : letI : Algebra A B := f.toRingHom.toAlgebra; Module.finrank A B = 1) :
    letI := ProjIntegral.integral G hG
    letI := ProjIntegral.integral H hH
    letI : Algebra (Proj G).functionField (Proj H).functionField :=
      (ProjFunctionFieldMap.map f hf hG hH hinj).toAlgebra
    (Proj G).functionField ≃ₐ[(Proj G).functionField] (Proj H).functionField := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let := ProjIntegral.integral G hG
  let := ProjIntegral.integral H hH
  let : Algebra (Proj G).functionField (Proj H).functionField :=
    (ProjFunctionFieldMap.map f hf hG hH hinj).toAlgebra
  have hfield := (ProjFunctionFieldRank.finrank_eq_module f hf hG hH hinj hb hb0 v w hv hgen).trans hr
  exact RankOneFieldSquares.equiv hfield

include hb hb0 hv in
theorem isSquare_iff_of_module_rank_one
    (hgen : letI : Algebra A B := f.toRingHom.toAlgebra
      Submodule.span A (Set.range v) = ⊤)
    (hr : letI : Algebra A B := f.toRingHom.toAlgebra; Module.finrank A B = 1) :
    letI := ProjIntegral.integral G hG
    letI := ProjIntegral.integral H hH
    letI : Algebra (Proj G).functionField (Proj H).functionField :=
      (ProjFunctionFieldMap.map f hf hG hH hinj).toAlgebra
    ∀ a : (Proj G).functionField, IsSquare (algebraMap (Proj G).functionField (Proj H).functionField a) ↔ IsSquare a := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let := ProjIntegral.integral G hG
  let := ProjIntegral.integral H hH
  let : Algebra (Proj G).functionField (Proj H).functionField :=
    (ProjFunctionFieldMap.map f hf hG hH hinj).toAlgebra
  intro a
  exact RankOneFieldSquares.equiv_isSquare_iff
    (equiv_of_module_rank_one f hf hG hH hinj hb hb0 v w hv hgen hr) a

end PaperP1.ProjFunctionFieldRankOne
