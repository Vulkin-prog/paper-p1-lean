module

public import PaperP1.Geometry.ProjRadicalMapCharts
public import PaperP1.Geometry.GradedFieldChartEvaluation
public import PaperP1.Geometry.AlgClosedAffineFieldPointLift

/-! # Exact coefficient-preserving affine-chart lifts from actual projective image membership -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.ProjRadicalFieldChartLift

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

variable {A B σ τ K : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] [Field K] [IsAlgClosed K]
  {G : ℕ → σ} {H : ℕ → τ} [GradedRing G] [GradedRing H]
  (f : G →+*ᵍ H)
  (hf : (HomogeneousIdeal.irrelevant H).toIdeal ≤
    ((HomogeneousIdeal.irrelevant G).toIdeal.map f.toRingHom).radical)
  [LocallyOfFiniteType (ProjRadicalMap.map f hf)]

include hf in
theorem chart_locally_finite_type {b : A} (hbg : b ∈ G 1) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Away.map f b))) := by
  let j := Proj.awayι G b hbg (by decide)
  have he := ProjRadicalMapCharts.chart_comp f hf (by decide : 0 < 1) b hbg
  have hl : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Away.map f b)) ≫ j) := by
    rw [← he]
    infer_instance
  let := hl
  exact locallyOfFiniteType_of_comp (Spec.map (CommRingCat.ofHom (Away.map f b))) j

theorem exists_chart_hom (ε : A →+* K) {b : A} (hb : ε b ≠ 0) (hbg : b ∈ G 1)
    (hy : GradedFieldChartEvaluation.pointMap G ε hb hbg (IsLocalRing.closedPoint K) ∈
      Set.range (ProjRadicalMap.map f hf)) :
    ∃ ψ : Away H (f b) →+* K,
      ψ.comp (Away.map f b) = GradedFieldChartEvaluation.evaluation G ε b hb := by
  let j := Proj.awayι G b hbg (by decide)
  let j' := Proj.awayι H (f b) (f.map_mem hbg) (by decide)
  let ρ := GradedFieldChartEvaluation.evaluation G ε b hb
  obtain ⟨q, hq⟩ := hy
  have hyo : GradedFieldChartEvaluation.pointMap G ε hb hbg (IsLocalRing.closedPoint K) ∈
      Proj.basicOpen G b := by
    rw [← Proj.opensRange_awayι G b hbg (by decide)]
    exact ⟨Spec.map (CommRingCat.ofHom ρ) (IsLocalRing.closedPoint K), rfl⟩
  have hqo : q ∈ Proj.basicOpen H (f b) := by
    change ProjRadicalMap.map f hf q ∈ Proj.basicOpen G b
    rw [hq]
    exact hyo
  have hqr : q ∈ Set.range j' := by
    change q ∈ j'.opensRange
    rw [Proj.opensRange_awayι]
    exact hqo
  obtain ⟨z, hz⟩ := hqr
  have hn := congrArg (fun g : Spec (CommRingCat.of (Away H (f b))) ⟶ Proj G ↦ g z)
    (ProjRadicalMapCharts.chart_comp f hf (by decide : 0 < 1) b hbg)
  have hze : PrimeSpectrum.comap (Away.map f b) z =
      PrimeSpectrum.comap ρ (IsLocalRing.closedPoint K) := by
    apply j.isOpenEmbedding.injective
    exact hn.symm.trans ((congrArg (ProjRadicalMap.map f hf) hz).trans hq)
  let : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Away.map f b))) :=
    chart_locally_finite_type f hf hbg
  exact AlgClosedAffineFieldPointLift.exists_hom (Away.map f b) ρ ⟨z, hze⟩

theorem exists_homogeneous_lift (ε : A →+* K) {b : A} (hb : ε b ≠ 0) (hbg : b ∈ G 1)
    (hy : GradedFieldChartEvaluation.pointMap G ε hb hbg (IsLocalRing.closedPoint K) ∈
      Set.range (ProjRadicalMap.map f hf)) :
    ∃ ρ : B →+* K, ∀ (n : ℕ) (P : A), P ∈ G n →
      ρ (f P) = ε P / ε b ^ n := by
  obtain ⟨ψ, hψ⟩ := exists_chart_hom f hf ε hb hbg hy
  let ρ := ψ.comp (GradedDehomogenization.map H (f.map_mem hbg))
  refine ⟨ρ, ?_⟩
  intro n P hP
  have he := RingHom.congr_fun (GradedDehomogenization.map_natural G hbg f) P
  change Away.map f b (GradedDehomogenization.map G hbg P) =
    GradedDehomogenization.map H (f.map_mem hbg) (f P) at he
  change ψ (GradedDehomogenization.map H (f.map_mem hbg) (f P)) = _
  rw [← he]
  change (ψ.comp (Away.map f b)) (GradedDehomogenization.map G hbg P) = _
  rw [hψ, GradedFieldChartEvaluation.evaluation_dehomogenization G ε hb hbg n P hP]

end PaperP1.ProjRadicalFieldChartLift
