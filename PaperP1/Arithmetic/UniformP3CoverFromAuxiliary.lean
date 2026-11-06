module

public import PaperP1.Arithmetic.UniformP3AuxiliaryHypersurface
public import PaperP1.Arithmetic.P3SingleAuxiliaryCurveCover
public import PaperP1.Analysis.P3AuxiliaryCoverExponentBudget
public import Mathlib.Algebra.Order.Archimedean.Basic

/-! # The complete primary P³ curve/exception cover follows from one quantitative global auxiliary equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformP3CoverFromAuxiliary

attribute [local instance] MvPolynomial.gradedAlgebra

theorem uniformCover (d : ℕ) (haux : UniformP3AuxiliaryHypersurface.UniformAuxiliary d) :
    UniformP3HypersurfaceCover.UniformCover d := by
  intro δ hδ
  have hδ4 : 0 < δ / 4 := by positivity
  obtain ⟨B, hB, hauxiliary⟩ := haux (δ / 4) hδ4
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ4
  obtain ⟨L, hL, hlog⟩ := UniformBinaryLogBudget.absorption 17 (δ / 4) hδ4
  let M := m + 1
  let K : ℝ := (d : ℝ) * B
  let C : ℝ := UniformIntegralCurveCount.constant.{0} 4
  let A : ℝ := 1 + K + C * K ^ 2 * L
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hC : 0 < C := UniformIntegralCurveCount.constant_pos.{0} 4
  have hprod : 0 ≤ C * K ^ 2 * L := by positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hKA : K ≤ A := by dsimp [A]; linarith only [hprod]
  have hCA : C * K ^ 2 * L ≤ A := by dsimp [A]; linarith only [hK]
  have hM : 0 < M := by dsimp [M]; omega
  have hMbudget : 1 / (M : ℝ) ≤ δ / 4 := by
    simpa only [M, Nat.cast_add, Nat.cast_one] using hm.le
  refine ⟨M, A, hA, ?_⟩
  intro I hI
  let := HomogeneousQuotientGrading.grading (MvPolynomial.homogeneousSubmodule (Fin 4) ℚ) I hI
  intro q hspan hgeom hq hdegree N hN U hU
  obtain ⟨e, G, hG, hnot, he, hzero⟩ := hauxiliary q hgeom hq hdegree N hN
  obtain ⟨T, family, hTU, hdegrees, hcard, hTbound, hcover⟩ := P3SingleAuxiliaryCurveCover.cover_of_equation
    I hI d q hspan hgeom hq hdegree e G hG hnot M N hM hN U hU
      (fun v hv ↦ hzero v (hU hv))
  let a : ℝ := 1 / Real.sqrt (d : ℝ)
  have hEd : ((e * d : ℕ) : ℝ) ≤ K * (N : ℝ) ^ (a + δ / 4) := by
    calc
      ((e * d : ℕ) : ℝ) = (d : ℝ) * (e : ℝ) := by push_cast; ring
      _ ≤ (d : ℝ) * (B * (N : ℝ) ^ (a + δ / 4)) :=
        mul_le_mul_of_nonneg_left he (Nat.cast_nonneg d)
      _ = _ := by dsimp [K]; ring
  have hfamily : (family.card : ℝ) ≤ A * (N : ℝ) ^ (a + δ) :=
    (show (family.card : ℝ) ≤ ((e * d : ℕ) : ℝ) by exact_mod_cast hcard).trans
      (P3AuxiliaryCoverExponentBudget.family_bound N hN a δ _ K A hδ.le hK hEd hKA)
  have hT : (T.card : ℝ) ≤ A * (N : ℝ) ^ (2 * a + δ) :=
    hTbound.trans (P3AuxiliaryCoverExponentBudget.exception_bound N hN a δ _ C K L A
      (Nat.cast_nonneg (e * d)) hC.le hL.le hEd (hlog N hN) M hMbudget hCA)
  have hexponent : 2 * a + δ = 2 / Real.sqrt (d : ℝ) + δ := by dsimp [a]; ring
  refine ⟨T, family, hTU, hdegrees, ?_, hfamily, hcover⟩
  simpa only [hexponent] using hT

end PaperP1.UniformP3CoverFromAuxiliary
