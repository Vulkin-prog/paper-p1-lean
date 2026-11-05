module

public import PaperP1.Algebra.MvPlaneBezout
public import PaperP1.Analysis.NonstationaryTangentImage
public import PaperP1.Analysis.LocalWronskianNonvanishing

/-! # Low-degree polynomial restrictions and finite Wronskian exceptions

Finite Bezout proves the local independence of the actual restrictions.
One genuine nonstationary trajectory suffices for polynomial nondivisibility.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurvePolynomialWronskianNonvanishing

open MvPolynomial Finset Set PolynomialTangentTrajectory NonstationaryTangentImage
open scoped ContDiff

def polynomialCombination {n : ℕ} (f : Fin n → MvPolynomial (Fin 2) ℝ)
    (c : Fin n → ℝ) : MvPolynomial (Fin 2) ℝ := ∑ i, C (c i) * f i

theorem combination_evaluation {n : ℕ} (f : Fin n → MvPolynomial (Fin 2) ℝ)
    (c : Fin n → ℝ) (z : Fin 2 → ℝ) :
    eval z (polynomialCombination f c) = ∑ i, c i * eval z (f i) := by
  simp only [polynomialCombination, map_sum, map_mul, eval_C]

theorem combination_degree {n : ℕ} (f : Fin n → MvPolynomial (Fin 2) ℝ)
    (k : ℕ) (hf : ∀ i, (f i).totalDegree ≤ k) (c : Fin n → ℝ) :
    (polynomialCombination f c).totalDegree ≤ k := by
  apply totalDegree_finsetSum_le
  intro i _hi
  exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hf i)

theorem restrictions_independent (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (n k : ℕ) (hk : k < P.totalDegree) (f : Fin n → MvPolynomial (Fin 2) ℝ)
    (hf : ∀ i, (f i).totalDegree ≤ k)
    (hcoeff : ∀ c : Fin n → ℝ, c ≠ 0 → polynomialCombination f c ≠ 0)
    (φ : Fin 2 → ℝ → ℝ) (a b : ℝ) (hφ : Trajectory P φ (Ioo a b))
    (hcurve : ∀ t ∈ Ioo a b, eval (position φ t) P = 0)
    (hnon : ∀ t ∈ Ioo a b, ∃ i, velocity P (position φ t) i ≠ 0) :
    LocalLinearIndependence.Independent (fun i t ↦ eval (position φ t) (f i)) (Ioo a b) := by
  intro u v huv hsub c hc
  have him := image_infinite_subinterval P φ (Ioo a b) hφ hnon u v huv hsub
  obtain ⟨z, hz, hzero⟩ := MvPlaneBezout.exists_nonzero_on_curve P (polynomialCombination f c) hP
    (hcoeff c hc) ((combination_degree f k hf c).trans_lt hk) (position φ '' Ioo u v) him (by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := hz
      exact hcurve t (hsub ht))
  obtain ⟨t, ht, rfl⟩ := hz
  refine ⟨t, ht, ?_⟩
  simpa only [combination_evaluation, RecursiveChebyshev.combination] using hzero

theorem wronskian_not_dvd (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (n k : ℕ) (hk : k < P.totalDegree) (f : Fin n → MvPolynomial (Fin 2) ℝ)
    (hf : ∀ i, (f i).totalDegree ≤ k)
    (hcoeff : ∀ c : Fin n → ℝ, c ≠ 0 → polynomialCombination f c ≠ 0)
    (φ : Fin 2 → ℝ → ℝ) (a b : ℝ) (hab : a < b) (hφ : Trajectory P φ (Ioo a b))
    (hcurve : ∀ t ∈ Ioo a b, eval (position φ t) P = 0)
    (hnon : ∀ t ∈ Ioo a b, ∃ i, velocity P (position φ t) i ≠ 0) :
    ¬P ∣ PolynomialTangentWronskian.wronskian P n f := by
  have hind := restrictions_independent P hP n k hk f hf hcoeff φ a b hφ hcurve hnon
  have hsmooth := contDiffOn_trajectory P φ (Ioo a b) isOpen_Ioo hφ
  obtain ⟨t, ht, hW⟩ := LocalWronskianNonvanishing.exists_nonzero n a b hab
    (fun i t ↦ eval (position φ t) (f i))
    (fun i ↦ PolynomialEvaluationDerivative.contDiffOn_eval (f i) ∞ (Ioo a b) φ hsmooth) hind
  have hWpoly : eval (position φ t) (PolynomialTangentWronskian.wronskian P n f) ≠ 0 := by
    change eval (fun j ↦ φ j t) (PolynomialTangentWronskian.wronskian P n f) ≠ 0
    rw [← wronskian_evaluation P φ (Ioo a b) isOpen_Ioo hφ n f t ht]
    exact hW
  rintro ⟨A, hA⟩
  rw [hA, map_mul, hcurve t ht, zero_mul] at hWpoly
  exact hWpoly rfl

theorem exceptional_card (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (n k : ℕ) (hk : k < P.totalDegree) (f : Fin n → MvPolynomial (Fin 2) ℝ)
    (hf : ∀ i, (f i).totalDegree ≤ k)
    (hcoeff : ∀ c : Fin n → ℝ, c ≠ 0 → polynomialCombination f c ≠ 0)
    (φ : Fin 2 → ℝ → ℝ) (a b : ℝ) (hab : a < b) (hφ : Trajectory P φ (Ioo a b))
    (hcurve : ∀ t ∈ Ioo a b, eval (position φ t) P = 0)
    (hnon : ∀ t ∈ Ioo a b, ∃ i, velocity P (position φ t) i ≠ 0)
    (S : Finset (Fin 2 → ℝ))
    (hS : ∀ z ∈ S, eval z P = 0 ∧ eval z (PolynomialTangentWronskian.wronskian P n f) = 0) :
    S.card ≤ P.totalDegree * (n * k + (n * (n - 1) / 2) * P.totalDegree) := by
  have hnot := wronskian_not_dvd P hP n k hk f hf hcoeff φ a b hab hφ hcurve hnon
  exact (MvPlaneBezout.common_points_card P _ hP hnot S hS).trans
    (Nat.mul_le_mul_left _ (PolynomialTangentWronskian.wronskian_degree_triangular P n k f hf))

end PaperP1.CurvePolynomialWronskianNonvanishing
