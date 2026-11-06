module

public import PaperP1.Geometry.OrdinarySurfaceCurveRegrading

/-! # A finite actual source-curve family gives actual ordinary image curves without increasing its size or degree cap -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceCurveOrdinaryImageFamily

open HomogeneousSplitRadicalData SourceProjectiveCurveData

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance

variable (s : List (PolynomialRing ℚ)) (c : Fin s.length → ℚ) (E : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * E - ((I i).card + (J i).card)) (I i) (J i))
  (hmin : ∀ i, 2 ≤ (I i).card + (J i).card)
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * E) (hE : 0 < E)

include hmin in
theorem exists_family (D : ℕ) (hD : 0 < D) (family : Finset (Curve s c E I J hdeg hE)) (B : ℕ)
    (hB : ∀ Γ ∈ family, degree s c E I J hs hdeg hE Γ ≤ (B : ℚ)) :
    ∃ curves : Finset (OrdinarySurfaceCurveData.Curve c D I J),
      curves.card ≤ family.card ∧ (∀ Δ ∈ curves, Δ.degree ≤ B) ∧
      ∀ Γ ∈ family, OrdinaryCurveSourcePoint.sourceZ c E I J ∉ sourceIdeal s c E I J hdeg hE Γ →
        ∃ Δ ∈ curves, Δ.ideal = SourceCurveOrdinaryImagePrime.ideal c E hE I J
          (sourceIdeal s c E I J hdeg hE Γ) := by
  classical
  let good := family.filter fun Γ ↦ OrdinaryCurveSourcePoint.sourceZ c E I J ∉ sourceIdeal s c E I J hdeg hE Γ
  have hex (Γ : {Γ // Γ ∈ good}) : ∃ Δ : OrdinarySurfaceCurveData.Curve c D I J,
      Δ.ideal = SourceCurveOrdinaryImagePrime.ideal c E hE I J (sourceIdeal s c E I J hdeg hE Γ.val) ∧
        (Δ.degree : ℚ) ≤ degree s c E I J hs hdeg hE Γ.val := by
    obtain ⟨Δ, hi, hd, _⟩ := OrdinarySurfaceCurveRegrading.source_curve_at_degree s c E I J hs hmin hdeg hE
      Γ.val (Finset.mem_filter.mp Γ.property).2 D hD
    exact ⟨Δ, hi, hd⟩
  choose image hideal hdegree using hex
  let curves := good.attach.image image
  refine ⟨curves, ?_, ?_, ?_⟩
  · exact (Finset.card_image_le.trans (by simp only [Finset.card_attach]; exact Finset.card_filter_le _ _))
  · intro Δ hΔ
    obtain ⟨Γ, _hΓ, rfl⟩ := Finset.mem_image.mp hΔ
    have hd : ((image Γ).degree : ℚ) ≤ (B : ℚ) :=
      (hdegree Γ).trans (hB Γ.val (Finset.mem_filter.mp Γ.property).1)
    exact_mod_cast hd
  · intro Γ hΓ hz
    have hgood : Γ ∈ good := Finset.mem_filter.mpr ⟨hΓ, hz⟩
    exact ⟨image ⟨Γ, hgood⟩, Finset.mem_image.mpr ⟨⟨Γ, hgood⟩, Finset.mem_attach _ _, rfl⟩,
      hideal ⟨Γ, hgood⟩⟩

end PaperP1.SourceCurveOrdinaryImageFamily
