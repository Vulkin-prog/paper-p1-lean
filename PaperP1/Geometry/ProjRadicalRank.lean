module

public import PaperP1.Geometry.ProjRadicalFlat
public import PaperP1.Algebra.GradedChartBasis
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # The finite flat projective map has its computed affine chart rank -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u v

namespace PaperP1.ProjRadicalRank

open AlgebraicGeometry CategoryTheory HomogeneousLocalization Module AlgebraicGeometry.Proj

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {G : ℕ → σ} {H : ℕ → τ} [GradedRing G] [GradedRing H]
  (f : G →+*ᵍ H)
  (hf : (HomogeneousIdeal.irrelevant H).toIdeal ≤
    ((HomogeneousIdeal.irrelevant G).toIdeal.map f.toRingHom).radical)

set_option backward.isDefEq.respectTransparency false in
theorem chart_pullback {b : A} (hb : b ∈ G 1) :
    IsPullback (awayι H (f b) (f.map_mem hb) (by decide : 0 < 1))
      (Spec.map (CommRingCat.ofHom (Away.map f b))) (ProjRadicalMap.map f hf)
      (awayι G b hb (by decide : 0 < 1)) := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · exact ProjRadicalCharts.chart_comp_map f hf (by decide : 0 < 1) b hb
  · rw [opensRange_awayι, opensRange_awayι]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem rank_on_chart {b : A} (hb : b ∈ G 1)
    [Flat (ProjRadicalMap.map f hf)] [IsFinite (ProjRadicalMap.map f hf)]
    [Nontrivial (Away G b)] {ι : Type v} [Fintype ι]
    (e : letI : Algebra (Away G b) (Away H (f b)) := (Away.map f b).toAlgebra;
      Basis ι (Away G b) (Away H (f b))) (p : PrimeSpectrum (Away G b)) :
    (ProjRadicalMap.map f hf).finrank (awayι G b hb (by decide : 0 < 1) p) = Fintype.card ι := by
  let : Algebra (Away G b) (Away H (f b)) := (Away.map f b).toAlgebra
  have : Module.Free (Away G b) (Away H (f b)) := .of_basis e
  have : Module.Finite (Away G b) (Away H (f b)) := .of_basis e
  rw [← Scheme.Hom.finrank_of_isPullback _ _ _ _ (chart_pullback f hf hb) p]
  change (Spec.map (CommRingCat.ofHom (algebraMap (Away G b) (Away H (f b))))).finrank p = _
  rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  exact Module.finrank_eq_card_basis e

end PaperP1.ProjRadicalRank
