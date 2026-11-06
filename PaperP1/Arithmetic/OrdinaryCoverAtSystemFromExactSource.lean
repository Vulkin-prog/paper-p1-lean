module

public import PaperP1.Arithmetic.ExactDegreeSourceSurfaceCover
public import PaperP1.Arithmetic.OrdinarySourceFiniteCoverTransfer

/-! # The exact genuine-degree source cover gives an actual ordinary cover at height H with source height H^E -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryCoverAtSystemFromExactSource

open HomogeneousSplitRadicalData WeightedOrdinaryAffineIdeal

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance

theorem exists_cover (k E : ℕ) (hE : 0 < E) (B : ℕ) (A δ : ℝ)
    (hcover : ExactDegreeSourceSurfaceCover.CoverAtSize k E hE B A δ)
    (s : List (PolynomialRing ℚ)) (hlen : s.length = k) (c : Fin k → ℚ) (I J : Fin k → Finset ℤ)
    (hs : ∀ i : Fin s.length, s.get i = radicand (c (Fin.cast hlen i))
      (2 * E - ((I (Fin.cast hlen i)).card + (J (Fin.cast hlen i)).card)) (I (Fin.cast hlen i)) (J (Fin.cast hlen i)))
    (hmin : ∀ i, 2 ≤ (I i).card + (J i).card) (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * E)
    (hc : ∀ i, c i ≠ 0) (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j))
    (D : ℕ) (hD : 0 < D) (H : ℕ) (hH : 1 ≤ H) (U : Finset (OrdinaryIntegerPoints.Point (Fin k)))
    (hU : U ⊆ OrdinaryIntegerPoints.curvePoints (ordinaryIdeal c I J) H) :
    ∃ (W : Finset (OrdinaryIntegerPoints.Point (Fin k))) (curves : Finset (OrdinarySurfaceCurveData.Curve c D I J)),
      W ⊆ U ∧ (∀ Δ ∈ curves, Δ.degree ≤ B) ∧
      (W.card : ℝ) ≤ A * ((H ^ E : ℕ) : ℝ) ^ (2 / Real.sqrt ((2 ^ k * E ^ 2 : ℕ) : ℝ) + δ) ∧
      (curves.card : ℝ) ≤ A * ((H ^ E : ℕ) : ℝ) ^ (1 / Real.sqrt ((2 ^ k * E ^ 2 : ℕ) : ℝ) + δ) ∧
      ∀ v ∈ U, v ∉ W → ∃ Δ ∈ curves, v ∈ OrdinaryIntegerPoints.curvePoints Δ.ideal H := by
  classical
  subst k
  let U' := U.image (OrdinarySourceIntegerLift.point E)
  have hU' : U' ⊆ SourceIntegerPoints.curvePoints E
      (RingHom.ker (SourceProjectiveEmbedding.evaluation c E I J hdeg hE).toRingHom) (H ^ E) := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact OrdinarySourcePointTransport.point_mem_global c E I J hdeg hE H v (hU hv) hH
  have hHE : 1 ≤ H ^ E := one_le_pow₀ hH
  obtain ⟨V, family, _hV, hdegrees, hVbound, hcount, hpoints⟩ :=
    hcover s rfl c I J hs hdeg hc hne hI hJ (H ^ E) hHE U' hU'
  have hpoints' : ∀ v ∈ U, OrdinarySourceIntegerLift.point E v ∉ V → ∃ Γ ∈ family,
      OrdinarySourceIntegerLift.point E v ∈ SourceIntegerPoints.curvePoints E
        (SourceProjectiveCurveData.ideal s c E I J hdeg hE Γ) (H ^ E) := by
    intro v hv hnot
    exact hpoints _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩) hnot
  obtain ⟨W, curves, hW, hWcard, hcard, hdegrees', hresult⟩ :=
    OrdinarySourceFiniteCoverTransfer.exists_cover s c E I J hs hmin hdeg hE D hD H (H ^ E)
      U hU V family B hdegrees hpoints'
  refine ⟨W, curves, hW, hdegrees', ?_, ?_, hresult⟩
  · exact (show (W.card : ℝ) ≤ (V.card : ℝ) by exact_mod_cast hWcard).trans hVbound
  · exact (show (curves.card : ℝ) ≤ (family.card : ℝ) by exact_mod_cast hcard).trans hcount

end PaperP1.OrdinaryCoverAtSystemFromExactSource
