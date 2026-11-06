module

public import PaperP1.Diophantine.GraphPlanePointCounts
public import PaperP1.Algebra.P3GraphPlaneKernel
public import PaperP1.Algebra.HomogeneousLastChartNonzero
public import PaperP1.Diophantine.FiniteFieldPolynomialZeroBound

/-! # Every actual section of a geometrically irreducible higher-degree surface is nonzero and has the coarse curve bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GraphPlaneCoarsePointCount

open MvPolynomial Finset P3GraphPlaneSection GraphPlanePointCounts
open scoped Classical

theorem map_section {F K : Type} [CommRing F] [CommRing K] (φ : F →+* K)
    (a : Fin 3 → F) (P : MvPolynomial (Fin 4) F) :
    map φ (planeSection a P) = planeSection (φ ∘ a) (map φ P) := by
  have he : (MvPolynomial.map φ).comp (planeSection a) =
      (planeSection (φ ∘ a)).comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [planeSection]
    · intro i
      cases i using Fin.cases <;> simp [planeSection, coordinates, form]
  exact RingHom.congr_fun he P

theorem geometric_section_ne_zero {F : Type} [Field F]
    (P : MvPolynomial (Fin 4) F) {d : ℕ} (hd : 1 < d) (hP : P.IsHomogeneous d)
    (hgeom : Irreducible (map (algebraMap F (AlgebraicClosure F)) P)) (a : Fin 3 → F) :
    planeSection a P ≠ 0 := by
  let φ := algebraMap F (AlgebraicClosure F)
  have hn := P3GraphPlaneKernel.section_ne_zero (map φ P) hd (hP.map φ) hgeom (φ ∘ a)
  intro hz
  apply hn
  rw [← map_section, hz, map_zero]

theorem section_card_le {F : Type} [Field F] [Fintype F]
    (P : MvPolynomial (Fin 4) F) {d : ℕ} (hd : 1 < d) (hP : P.IsHomogeneous d)
    (hgeom : Irreducible (map (algebraMap F (AlgebraicClosure F)) P)) (a : Fin 3 → F) :
    (affineZeros (planeSection a P)).card ≤ d * Fintype.card F := by
  have hhom := section_homogeneous a P hP
  have hn := HomogeneousLastChartNonzero.chart_ne_zero _ hhom
    (geometric_section_ne_zero P hd hP hgeom a)
  have hb := FiniteFieldPolynomialZeroBound.cardinality (by decide : 0 < 2)
    (LastChartPolynomial.dehomogenize (planeSection a P)) hn (affineZeros (planeSection a P)) (by
      intro u hu
      rw [LastChartPolynomial.evaluation]
      exact (mem_filter.mp hu).2)
  have hdeg := HomogeneousLastChartNonzero.chart_degree_le _ hhom
  have hb' : (affineZeros (planeSection a P)).card ≤
      (LastChartPolynomial.dehomogenize (planeSection a P)).totalDegree * Fintype.card F := by
    simpa only [show (2 : ℕ) - 1 = 1 by decide, pow_one] using hb
  exact hb'.trans (Nat.mul_le_mul_right _ hdeg)

theorem surface_card_le {F : Type} [Field F] [Fintype F]
    (P : MvPolynomial (Fin 4) F) {d : ℕ} (hP : P.IsHomogeneous d) (hP0 : P ≠ 0) :
    (affineZeros P).card ≤ d * Fintype.card F ^ 2 := by
  have hn := HomogeneousLastChartNonzero.chart_ne_zero P hP hP0
  have hb := FiniteFieldPolynomialZeroBound.cardinality (by decide : 0 < 3)
    (LastChartPolynomial.dehomogenize P) hn (affineZeros P) (by
      intro u hu
      rw [LastChartPolynomial.evaluation]
      exact (mem_filter.mp hu).2)
  exact hb.trans (Nat.mul_le_mul_right _ (HomogeneousLastChartNonzero.chart_degree_le P hP))

end PaperP1.GraphPlaneCoarsePointCount
