module

public import PaperP1.Arithmetic.ActualSourceSurfaceProjectionExceptionalCurves
public import PaperP1.Arithmetic.ActualSourceProjectedCurveFamilyCover

/-! # The actual source surface cover reduces to the actual projected hypersurface cover with explicit curve and exception budgets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualSourceSurfaceCoverReduction

open MvPolynomial HomogeneousSplitRadicalData SourceProjectiveEmbedding SourceVeroneseGrading
  SourceSurfaceBoundedProjection SourceIntegerHypersurfaceProjection SourceProjectiveCurveData

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance
local instance indexFinite (k D : ℕ) : Finite (GeneratorIndex ℚ (Fin k) D) := index_finite ℚ (Fin k) D
local instance indexFintype (k D : ℕ) : Fintype (GeneratorIndex ℚ (Fin k) D) := Fintype.ofFinite _

theorem exists_projection_with_cover_transfer (s : List (PolynomialRing ℚ)) (c : Fin s.length → ℚ)
    (D : ℕ) (hD : 0 < D) (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
    (hc : ∀ i, c i ≠ 0) (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j))
    (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    ∃ (u : GeneratorIndex ℚ (Fin s.length) D → ℕ) (q : MvPolynomial (Fin 4) ℚ),
      (∀ i, u i ≤ coefficientBound s.length D) ∧
      LinearHypersurfaceImage.ideal (F := ℚ) (SourceSurfacePowerParameters.parameters s c D hD I J hs)
        (primitive c D I J u) = Ideal.span {q} ∧
      Irreducible q ∧ Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) q) ∧
      q.IsHomogeneous (2 ^ s.length * D ^ 2) ∧ q.totalDegree = 2 ^ s.length * D ^ 2 ∧
      (finSuccEquiv ℚ 3 q).Monic ∧
      (∀ (H : ℕ) (v : GeneratorIndex ℚ (Fin s.length) D → ℤ),
        v ∈ SourceIntegerPoints.curvePoints D
          (RingHom.ker (SourceProjectiveEmbedding.evaluation c D I J hdeg hD).toRingHom) H →
        (∀ i, (projection D u v i).natAbs ≤ heightFactor s.length D * H) ∧
        projection D u v 3 = 1 ∧ eval (fun i ↦ (projection D u v i : ℚ)) q = 0) ∧
      letI := ActualSourceProjectedCurveFamilyCover.imageGrading s c D hD I J hs hdeg u;
      ∀ (H : ℕ) (U : Finset (GeneratorIndex ℚ (Fin s.length) D → ℤ))
        (_hU : U ⊆ SourceIntegerPoints.curvePoints D
          (RingHom.ker (SourceProjectiveEmbedding.evaluation c D I J hdeg hD).toRingHom) H)
        (M : ℕ) (T : Finset (Fin 4 → ℤ))
        (family : Finset (GradedProjectiveCurveData.Curve (LinearHypersurfaceImage.piece (F := ℚ)
          (SourceSurfacePowerParameters.parameters s c D hD I J hs) (primitive c D I J u))))
        (_hM : ∀ Γ ∈ family, Γ.degree ≤ (M : ℚ))
        (_htarget : ∀ v ∈ U, projection D u v ∉ T →
          ∃ Γ ∈ family, ∀ P ∈ SourceImageIntegerPointEvaluation.imageIdeal s c D hD I J hs u Γ.ideal,
            eval (fun i ↦ (projection D u v i : ℚ)) P = 0),
        ∃ (V : Finset (GeneratorIndex ℚ (Fin s.length) D → ℤ))
            (curves : Finset (Curve s c D I J hdeg hD)),
          V ⊆ U ∧ V.card ≤ T.card ∧
          curves.card ≤ (2 ^ s.length * D ^ 2 - 1) * (2 ^ s.length * D ^ 2) +
            family.card * (M * (2 ^ s.length * D ^ 2)) ∧
          (∀ Γ ∈ curves, degree s c D I J hs hdeg hD Γ ≤
            ((max ((2 ^ s.length * D ^ 2 - 1) * (2 ^ s.length * D ^ 2))
              (M * (2 ^ s.length * D ^ 2)) : ℕ) : ℚ)) ∧
          ∀ v ∈ U, v ∉ V → ∃ Γ ∈ curves,
            v ∈ SourceIntegerPoints.curvePoints D (SourceProjectiveCurveData.ideal s c D I J hdeg hD Γ) H := by
  classical
  obtain ⟨u, q, bad, hu, hideal, hirr, hgeom, hhom, htotal, hmonic, hbadcount, hbaddegree, hpoints⟩ :=
    ActualSourceSurfaceProjectionExceptionalCurves.exists_projection s c D hD I J hs hdeg hc hne hI hJ
  refine ⟨u, q, hu, hideal, hirr, hgeom, hhom, htotal, hmonic, ?_, ?_⟩
  · intro H v hv
    exact ⟨(hpoints H v hv).1, (hpoints H v hv).2.1, (hpoints H v hv).2.2.1⟩
  · let := ActualSourceProjectedCurveFamilyCover.imageGrading s c D hD I J hs hdeg u
    intro H U hU M T family hM htarget
    obtain ⟨lifted, hliftcount, hliftdegree, hliftcover⟩ :=
      ActualSourceProjectedCurveFamilyCover.uniform_family_cover s c D hD I J hs hdeg hc hne hI hJ u family M hM
    let good (v : GeneratorIndex ℚ (Fin s.length) D → ℤ) :=
      eval (fun i ↦ (projection D u v i : ℚ)) (pderiv 0 q) ≠ 0
    let V := U.filter (fun v ↦ good v ∧ projection D u v ∈ T)
    have hinj : Set.InjOn (projection D u) (V : Set _) := by
      intro v hv w hw he
      have hv' := Finset.mem_filter.mp hv
      have hw' := Finset.mem_filter.mp hw
      exact (hpoints H v (hU hv'.1)).2.2.2.2 w (hU hw'.1) he hv'.2.1
    have hVcard : V.card ≤ T.card := by
      calc
        V.card = (V.image (projection D u)).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ T.card := Finset.card_le_card (by
          intro w hw
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
          exact (Finset.mem_filter.mp hv).2.2)
    refine ⟨V, bad ∪ lifted, Finset.filter_subset _ _, hVcard, ?_, ?_, ?_⟩
    · exact (Finset.card_union_le _ _).trans (Nat.add_le_add hbadcount hliftcount)
    · intro Γ hΓ
      rcases Finset.mem_union.mp hΓ with hb | hl
      · exact (hbaddegree Γ hb).trans (by exact_mod_cast (le_max_left
          ((2 ^ s.length * D ^ 2 - 1) * (2 ^ s.length * D ^ 2)) (M * (2 ^ s.length * D ^ 2))))
      · exact (hliftdegree Γ hl).trans (by exact_mod_cast (le_max_right
          ((2 ^ s.length * D ^ 2 - 1) * (2 ^ s.length * D ^ 2)) (M * (2 ^ s.length * D ^ 2))))
    · intro v hv hvnot
      by_cases hgood : good v
      · have hnot : projection D u v ∉ T := fun ht ↦ hvnot (Finset.mem_filter.mpr ⟨hv, hgood, ht⟩)
        obtain ⟨Γ, hΓ, hvΓ⟩ := hliftcover H v (hU hv) (htarget v hv hnot)
        exact ⟨Γ, Finset.mem_union_right _ hΓ, hvΓ⟩
      · have hzero : eval (fun i ↦ (projection D u v i : ℚ)) (pderiv 0 q) = 0 := not_ne_iff.mp hgood
        obtain ⟨Γ, hΓ, hvΓ⟩ := (hpoints H v (hU hv)).2.2.2.1 hzero
        exact ⟨Γ, Finset.mem_union_left _ hΓ, hvΓ⟩

end PaperP1.ActualSourceSurfaceCoverReduction
