module

public import PaperP1.Geometry.SourceCurveOrdinaryImageFamily
public import PaperP1.Arithmetic.OrdinarySourcePointTransport

/-! # A literal finite source covering transfers to ordinary points with no increase of exceptions, curves or degree cap -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinarySourceFiniteCoverTransfer

open HomogeneousSplitRadicalData SourceProjectiveEmbedding SourceProjectiveCurveData WeightedOrdinaryAffineIdeal

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance

variable (s : List (PolynomialRing ℚ)) (c : Fin s.length → ℚ) (E : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * E - ((I i).card + (J i).card)) (I i) (J i))
  (hmin : ∀ i, 2 ≤ (I i).card + (J i).card)
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * E) (hE : 0 < E)

include hmin in
theorem exists_cover (D : ℕ) (hD : 0 < D) (H R : ℕ)
    (U : Finset (OrdinaryIntegerPoints.Point (Fin s.length)))
    (hU : U ⊆ OrdinaryIntegerPoints.curvePoints (ordinaryIdeal c I J) H)
    (V : Finset (GeneratorIndex ℚ (Fin s.length) E → ℤ))
    (family : Finset (Curve s c E I J hdeg hE)) (B : ℕ)
    (hB : ∀ Γ ∈ family, degree s c E I J hs hdeg hE Γ ≤ (B : ℚ))
    (hcover : ∀ v ∈ U, OrdinarySourceIntegerLift.point E v ∉ V → ∃ Γ ∈ family,
      OrdinarySourceIntegerLift.point E v ∈ SourceIntegerPoints.curvePoints E (ideal s c E I J hdeg hE Γ) R) :
    ∃ (W : Finset (OrdinaryIntegerPoints.Point (Fin s.length)))
      (curves : Finset (OrdinarySurfaceCurveData.Curve c D I J)),
      W ⊆ U ∧ W.card ≤ V.card ∧ curves.card ≤ family.card ∧ (∀ Δ ∈ curves, Δ.degree ≤ B) ∧
      ∀ v ∈ U, v ∉ W → ∃ Δ ∈ curves, v ∈ OrdinaryIntegerPoints.curvePoints Δ.ideal H := by
  classical
  obtain ⟨curves, hcard, hdegrees, hfamily⟩ :=
    SourceCurveOrdinaryImageFamily.exists_family s c E I J hs hmin hdeg hE D hD family B hB
  let W := U.filter fun v ↦ OrdinarySourceIntegerLift.point E v ∈ V
  have hW : W ⊆ U := Finset.filter_subset _ _
  have hnormal (v : OrdinaryIntegerPoints.Point (Fin s.length)) (hv : v ∈ U) : v (Sum.inl 2) = 1 :=
    ((OrdinaryIntegerPoints.mem_curvePoints _ H v).mp (hU hv)).1.2
  have hWcard : W.card ≤ V.card := by
    apply Finset.card_le_card_of_injOn (OrdinarySourceIntegerLift.point E)
    · intro v hv
      exact (Finset.mem_filter.mp hv).2
    · intro v hv w hw he
      exact OrdinarySourceIntegerLift.point_injOn E hE (hnormal v (hW hv)) (hnormal w (hW hw)) he
  refine ⟨W, curves, hW, hWcard, hcard, hdegrees, ?_⟩
  intro v hv hnot
  have hv' : OrdinarySourceIntegerLift.point E v ∉ V := by
    intro hh
    exact hnot (Finset.mem_filter.mpr ⟨hv, hh⟩)
  obtain ⟨Γ, hΓ, hpoint⟩ := hcover v hv hv'
  have hz : OrdinaryCurveSourcePoint.sourceZ c E I J ∉ sourceIdeal s c E I J hdeg hE Γ :=
    OrdinarySourcePointTransport.source_curve_chart_not_mem c E I J hdeg hE H v (hU hv)
      (sourceIdeal s c E I J hdeg hE Γ) R hpoint
  obtain ⟨Δ, hΔ, hideal⟩ := hfamily Γ hΓ hz
  refine ⟨Δ, hΔ, ?_⟩
  rw [hideal]
  exact OrdinarySourcePointTransport.ordinary_image_point c E I J hdeg hE H v (hU hv)
    (sourceIdeal s c E I J hdeg hE Γ) R hpoint

end PaperP1.OrdinarySourceFiniteCoverTransfer
