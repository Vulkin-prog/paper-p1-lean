module

public import PaperP1.Arithmetic.P3CoarseCanonicalClassCount
public import PaperP1.Arithmetic.IntegerProjectedModelNormalization
public import PaperP1.Algebra.AffineProjectionHypersurfacePoints

/-! # Every actual canonical smooth class injects into the literal normalized monic-model hypersurface solutions -/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.CanonicalClassesToMonicHypersurface
open Polynomial PaperP1.P3CanonicalSmoothResidues
open scoped Classical
variable (p : ℕ) [Fact p.Prime] (Q : MvPolynomial (Fin 4) ℤ)

def coordinates (r : Class p Q) : (Fin 2 → ZMod p) × ZMod p :=
  (Fin.tail (PaperP1.P3CoarseCanonicalClassCount.fieldCoordinates r.val),
    PaperP1.P3CoarseCanonicalClassCount.fieldCoordinates r.val 0)

omit [Fact p.Prime] in
theorem coordinates_injective : Function.Injective (coordinates p Q) := by
  intro r s he
  apply Subtype.ext
  apply PaperP1.P3CoarseCanonicalClassCount.fieldCoordinates_injective p
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact congrArg Prod.snd he
  · exact congrArg (fun tw : (Fin 2 → ZMod p) × ZMod p ↦ tw.1 j) he

theorem normalized_zero (b : ℤ) (r : Class p Q) :
    (PaperP1.MonicP3LastChart.chart (PaperP1.IntegerProjectedModelNormalization.normalized (ZMod p) Q b)).eval₂
      (MvPolynomial.eval (coordinates p Q r).1) (coordinates p Q r).2 = 0 := by
  let x := PaperP1.P3CoarseCanonicalClassCount.fieldCoordinates r.val
  have hroot := PaperP1.P3CoarseCanonicalClassCount.affine_zero p Q r
  rw [PaperP1.HomogeneousLastChartNonzero.map_chart, PaperP1.LastChartPolynomial.evaluation] at hroot
  have hnorm : MvPolynomial.aeval (Fin.snoc x 1)
      (PaperP1.IntegerProjectedModelNormalization.normalized (ZMod p) Q b) = 0 := by
    change MvPolynomial.eval (Fin.snoc x 1)
      (MvPolynomial.C (b : ZMod p)⁻¹ * MvPolynomial.map (Int.castRingHom (ZMod p)) Q) = 0
    rw [map_mul, hroot, mul_zero]
  have hh := PaperP1.MonicP3LastChart.evaluation
    (PaperP1.IntegerProjectedModelNormalization.normalized (ZMod p) Q b) (Fin.tail x) (x 0)
  rw [Fin.cons_self_tail] at hh
  exact hh.trans hnorm

def pointMap (b : ℤ) (r : Class p Q) : PaperP1.AffineProjectionHypersurfacePoints.Solution (ZMod p)
    (PaperP1.MonicP3LastChart.chart (PaperP1.IntegerProjectedModelNormalization.normalized (ZMod p) Q b)) :=
  ⟨coordinates p Q r, normalized_zero p Q b r⟩

theorem pointMap_injective (b : ℤ) : Function.Injective (pointMap p Q b) := by
  intro r s he
  exact coordinates_injective p Q (congrArg Subtype.val he)

theorem cardinality_le (b : ℤ) : Fintype.card (Class p Q) ≤
    Nat.card (PaperP1.AffineProjectionHypersurfacePoints.Solution (ZMod p)
      (PaperP1.MonicP3LastChart.chart (PaperP1.IntegerProjectedModelNormalization.normalized (ZMod p) Q b))) := by
  have hh := Nat.card_le_card_of_injective (pointMap p Q b) (pointMap_injective p Q b)
  simpa only [Nat.card_eq_fintype_card] using hh

end PaperP1.CanonicalClassesToMonicHypersurface
