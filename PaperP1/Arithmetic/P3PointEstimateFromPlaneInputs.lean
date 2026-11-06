module

public import PaperP1.Arithmetic.P3ClassicalPlanePointInputs
public import PaperP1.Algebra.AlgClosedPolynomialIrreducibility
public import PaperP1.Analysis.SquareRootPointErrorThreshold
public import PaperP1.Arithmetic.P3FiniteFieldBudgetFixedHeight
public import PaperP1.Arithmetic.UniformP3AuxiliaryFromFiniteFieldCertificate

/-! # Actual surface point bounds follow from explicit classical plane-curve and good-section inputs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3PointEstimateFromPlaneInputs

open MvPolynomial Finset P3GraphPlaneSection GraphPlanePointCounts
open P3GraphPlaneBadSectionCount P3ClassicalPlanePointInputs
open scoped Classical

theorem error_constants (d : ℕ) (hd : 1 < d)
    (hcurve : PlaneCurveUpperBound d) (hsection : GoodGraphSection d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ E K₀ : ℕ, ∀ (p : ℕ) (hp : p.Prime), K₀ ≤ p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ P : MvPolynomial (Fin 4) (ZMod p), P.IsHomogeneous d →
        Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) P) →
        ((affineZeros P).card : ℝ) ≤ (p : ℝ) ^ 2 + C * p * Real.sqrt p + (E : ℝ) * p := by
  obtain ⟨N, hN⟩ := GraphPlaneAverageUpperBound.uniform_surface_bound d hd
  obtain ⟨C, hC, KC, hcurve⟩ := hcurve
  obtain ⟨KS, hsection⟩ := hsection
  let E : ℕ := (d * N) * d
  refine ⟨C, hC, E, max KC KS, ?_⟩
  intro p hp hK
  let : Fact p.Prime := ⟨hp⟩
  intro P hP hgeom
  obtain ⟨a, ha⟩ := hsection p hp ((le_max_right KC KS).trans hK) P hP hgeom
  have hgood : Irreducible (map (algebraMap (AlgebraicClosure (ZMod p))
      (AlgebraicClosure (AlgebraicClosure (ZMod p))))
      (planeSection a (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) P))) :=
    (AlgClosedPolynomialIrreducibility.map_irreducible_iff _).mpr ha
  have hB : 0 ≤ (p : ℝ) + C * Real.sqrt p := add_nonneg (Nat.cast_nonneg p) (mul_nonneg hC (Real.sqrt_nonneg _))
  have hc : ∀ b ∈ goodSections P,
      ((affineZeros (planeSection b P)).card : ℝ) ≤ (p : ℝ) + C * Real.sqrt p := by
    intro b hb
    exact hcurve p hp ((le_max_left KC KS).trans hK) _ (section_homogeneous b P hP) (mem_filter.mp hb).2
  have hh := hN (ZMod p) (AlgebraicClosure (ZMod p)) P hP hgeom
    (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) a hgood _ hB hc
  simp only [ZMod.card] at hh
  apply hh.trans_eq
  simp only [E, Nat.cast_mul]
  ring

theorem uniform_estimate (d : ℕ) (hd : 1 < d)
    (hcurve : PlaneCurveUpperBound d) (hsection : GoodGraphSection d) :
    P3FiniteFieldClassEstimate.UniformEstimate d := by
  intro η hη
  obtain ⟨C, hC, E, KR, hR⟩ := error_constants d hd hcurve hsection
  obtain ⟨KE, hE⟩ := SquareRootPointErrorThreshold.exists_threshold C E η hC (by positivity) hη
  refine ⟨max KR KE, ?_⟩
  intro p hp hK P hP hgeom
  let : Fact p.Prime := ⟨hp⟩
  have hr := hR p hp ((le_max_left KR KE).trans hK)
    (map (Int.castRingHom (ZMod p)) P) (hP.map _) hgeom
  have hc : (Fintype.card (P3CanonicalSmoothResidues.Class p P) : ℝ) ≤
      ((affineZeros (map (Int.castRingHom (ZMod p)) P)).card : ℝ) := by
    exact_mod_cast GraphPlanePointCounts.canonical_card_le p hp P
  apply hc.trans (hr.trans ?_)
  have he := hE p ((le_max_right KR KE).trans hK)
  calc
    _ = (p : ℝ) ^ 2 + (C * p * Real.sqrt p + (E : ℝ) * p) := by ring
    _ ≤ (p : ℝ) ^ 2 + η * (p : ℝ) ^ 2 := add_le_add le_rfl he
    _ = (1 + η) * (p : ℝ) ^ 2 := by ring

theorem uniform_auxiliary (d : ℕ) (hd : 1 < d)
    (hcurve : PlaneCurveUpperBound d) (hsection : GoodGraphSection d) :
    UniformP3AuxiliaryHypersurface.UniformAuxiliary d :=
  UniformP3AuxiliaryFromFiniteFieldCertificate.uniform_auxiliary d
    (P3FiniteFieldBudgetFixedHeight.uniform_budget d (uniform_estimate d hd hcurve hsection))

end PaperP1.P3PointEstimateFromPlaneInputs
