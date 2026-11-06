module

public import PaperP1.Arithmetic.UniformNormalizedCurvePointCount
public import PaperP1.Arithmetic.FiniteIndexIntegralCurveCount
public import PaperP1.Analysis.UniformBinaryLogBudget

/-! # The actual normalized and ordinary bounded-degree curve properties have internal proofs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnconditionalNormalizedCurveCount

open DegreeUniformAffineParameters QuadraticDegreeUniformFieldCount
attribute [local instance] MvPolynomial.gradedAlgebra

def ambientConstant (nmax : ℕ) : ℝ :=
  1 + ∑ n ∈ Finset.range (nmax + 1), UniformIntegralCurveCount.constant.{0} n

theorem ambientConstant_pos (nmax : ℕ) : 0 < ambientConstant nmax := by
  have hh : 0 ≤ ∑ n ∈ Finset.range (nmax + 1), UniformIntegralCurveCount.constant.{0} n :=
    Finset.sum_nonneg (fun n _hn ↦ (UniformIntegralCurveCount.constant_pos.{0} n).le)
  unfold ambientConstant
  linarith only [hh]

theorem constant_le_ambient (n nmax : ℕ) (hn : n ≤ nmax) :
    UniformIntegralCurveCount.constant.{0} n ≤ ambientConstant nmax := by
  have hh : UniformIntegralCurveCount.constant.{0} n ≤
      ∑ j ∈ Finset.range (nmax + 1), UniformIntegralCurveCount.constant.{0} j :=
    Finset.single_le_sum (fun j _hj ↦ (UniformIntegralCurveCount.constant_pos.{0} j).le)
      (Finset.mem_range.mpr (by omega))
  exact hh.trans (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))

theorem uniform_bound (nmax M : ℕ) : UniformNormalizedCurvePointCount.UniformBound nmax M := by
  intro δ hδ
  obtain ⟨L, hL, hlog⟩ := UniformBinaryLogBudget.absorption 17 δ hδ
  let A : ℝ := ambientConstant nmax * ((M + 1 : ℕ) : ℝ) ^ 2 * L
  have hamb := ambientConstant_pos nmax
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro σ _hσ hdim Γ hM z H hH
  let d := ProjectiveCurveHilbertDegree.natDegree Γ
  have hd : 0 < d := ProjectiveCurveHilbertDegree.natDegree_pos Γ
  have hdQ : (d : ℚ) = Γ.degree := ProjectiveCurveHilbertDegree.natDegree_cast Γ
  have hdR : (d : ℝ) = (Γ.degree : ℝ) := by exact_mod_cast hdQ
  have hDM : d ≤ M := by
    have hh : (d : ℚ) ≤ (M : ℚ) := by rw [hdQ]; exact hM
    exact_mod_cast hh
  have hp : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (MvPolynomial.homogeneousSubmodule σ ℚ) Γ.ideal)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C Γ.constant) := by
    rw [hdQ]
    exact Γ.hilbert
  let S := NormalizedIntegerPoints.points Γ.ideal z H
  have hnormal : ∀ w ∈ S, w z = 1 := by
    intro w hw
    exact ((NormalizedIntegerPoints.mem_points Γ.ideal z H w).mp hw).1.2
  have hcurve : ∀ w ∈ S, ∀ P ∈ Γ.ideal, MvPolynomial.eval (fun i ↦ (w i : ℚ)) P = 0 := by
    intro w hw P hP
    exact ((NormalizedIntegerPoints.mem_points Γ.ideal z H w).mp hw).2 hP
  have hheight : ∀ w ∈ S, ∀ i, (w i).natAbs ≤ H := by
    intro w hw i
    have hh := ((NormalizedIntegerPoints.mem_points Γ.ideal z H w).mp hw).1.1 i
    rw [Int.abs_eq_natAbs] at hh
    exact_mod_cast hh
  have hc := FiniteIndexIntegralCurveCount.population_bound Γ.ideal Γ.homogeneous Γ.prime d hd
    Γ.constant hp z H hH S hnormal hcurve hheight
  have hdimC := constant_le_ambient (Nat.card σ) nmax hdim
  have hDMR : (d : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by exact_mod_cast hDM.trans (Nat.le_succ M)
  have hDsquare := pow_le_pow_left₀ (Nat.cast_nonneg d) hDMR 2
  have hlogs := hlog H hH
  have hC := UniformIntegralCurveCount.constant_pos.{0} (Nat.card σ)
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  change (S.card : ℝ) ≤ A * (H : ℝ) ^ (1 / (Γ.degree : ℝ) + δ)
  rw [← hdR]
  calc
    _ ≤ UniformIntegralCurveCount.constant.{0} (Nat.card σ) * profile d H := hc
    _ = UniformIntegralCurveCount.constant.{0} (Nat.card σ) * (d : ℝ) ^ 2 *
        (logarithmicBudget H : ℝ) ^ 17 * (H : ℝ) ^ (1 / (d : ℝ)) := by unfold profile; ring
    _ ≤ ambientConstant nmax * ((M + 1 : ℕ) : ℝ) ^ 2 *
        (L * (H : ℝ) ^ δ) * (H : ℝ) ^ (1 / (d : ℝ)) := by gcongr
    _ = _ := by rw [Real.rpow_add hHpos]; dsimp [A]; ring

theorem ordinary_bound (kmax M : ℕ) : UniformAffineCurvePointCount.UniformBound kmax M :=
  UniformNormalizedCurvePointCount.ordinary_specialization kmax M (uniform_bound (kmax + 3) M)

end PaperP1.UnconditionalNormalizedCurveCount
