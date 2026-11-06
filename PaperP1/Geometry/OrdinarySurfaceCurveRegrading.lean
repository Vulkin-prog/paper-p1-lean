module

public import PaperP1.Geometry.OrdinaryCurveVeroneseHeight
public import PaperP1.Geometry.SourceProjectiveCurveToOrdinary

/-! # Actual ordinary image curves retain their same ideal and degree at every positive auxiliary degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinarySurfaceCurveRegrading

open MvPolynomial HomogeneousSplitRadicalData

variable {ι : Type*} (c : ι → ℚ) (I J : ι → Finset ℤ) (E : ℕ) (hE : 0 < E)
  (hmin : ∀ i, 2 ≤ (I i).card + (J i).card) (Γ : OrdinarySurfaceCurveData.Curve c E I J)
  (hz : X (Sum.inl (2 : Fin 3)) ∉ Γ.ideal)

def regrade (D : ℕ) (hD : 0 < D) : OrdinarySurfaceCurveData.Curve c D I J := by
  let : Γ.ideal.IsPrime := Γ.prime
  exact {
    ideal := Γ.ideal
    prime := Γ.prime
    homogeneous := Γ.homogeneous
    relations := Γ.relations
    height := (OrdinaryCurveVeroneseHeight.height_independent c I J Γ.ideal Γ.relations hmin
      Γ.homogeneous hz D E hD hE).trans Γ.height
    degree := Γ.degree
    degree_pos := Γ.degree_pos
    constant := Γ.constant
    hilbert := Γ.hilbert }

theorem regrade_ideal (D : ℕ) (hD : 0 < D) : (regrade c I J E hE hmin Γ hz D hD).ideal = Γ.ideal := rfl

theorem regrade_degree (D : ℕ) (hD : 0 < D) : (regrade c I J E hE hmin Γ hz D hD).degree = Γ.degree := rfl

theorem source_curve_at_degree (s : List (PolynomialRing ℚ)) (c : Fin s.length → ℚ) (E : ℕ)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * E - ((I i).card + (J i).card)) (I i) (J i))
    (hmin : ∀ i, 2 ≤ (I i).card + (J i).card)
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * E) (hE : 0 < E)
    (Γ : SourceProjectiveCurveData.Curve s c E I J hdeg hE)
    (hz : OrdinaryCurveSourcePoint.sourceZ c E I J ∉ SourceProjectiveCurveData.sourceIdeal s c E I J hdeg hE Γ)
    (D : ℕ) (hD : 0 < D) :
    ∃ Δ : OrdinarySurfaceCurveData.Curve c D I J,
      Δ.ideal = SourceCurveOrdinaryImagePrime.ideal c E hE I J
        (SourceProjectiveCurveData.sourceIdeal s c E I J hdeg hE Γ) ∧
      (Δ.degree : ℚ) ≤ SourceProjectiveCurveData.degree s c E I J hs hdeg hE Γ ∧
      SourceProjectiveCurveData.degree s c E I J hs hdeg hE Γ ≤ (Δ.degree : ℚ) * (E : ℚ) := by
  obtain ⟨Δ, hΔ, hle, hreverse⟩ :=
    SourceProjectiveCurveToOrdinary.exists_curve s c E I J hs hmin hdeg hE Γ hz
  have hchart : X (Sum.inl (2 : Fin 3)) ∉ Δ.ideal := by
    rw [hΔ]
    exact SourceCurveOrdinaryImagePrime.chart_not_mem c E hE I J
      (SourceProjectiveCurveData.sourceIdeal s c E I J hdeg hE Γ) hz
  exact ⟨regrade c I J E hE hmin Δ hchart D hD, hΔ, hle, hreverse⟩

end PaperP1.OrdinarySurfaceCurveRegrading
