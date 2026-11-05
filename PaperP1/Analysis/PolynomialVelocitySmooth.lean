module

public import PaperP1.Analysis.PolynomialTangentTrajectory

/-! # Smoothness of actual multivariate evaluation and the polynomial velocity field

Here the domain is the full finite-dimensional coordinate space.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialVelocitySmooth

open MvPolynomial PolynomialTangentTrajectory

theorem contDiff_eval {σ : Type*} [Fintype σ] (Q : MvPolynomial σ ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun z : σ → ℝ ↦ eval z Q) := by
  induction Q using MvPolynomial.induction_on with
  | C r => simpa only [eval_C] using (contDiff_const (c := r) : ContDiff ℝ n (fun _ : σ → ℝ ↦ r))
  | add P Q hP hQ =>
    simp only [map_add]
    exact hP.add hQ
  | mul_X P i hP =>
    simp only [map_mul, eval_X]
    exact hP.mul (contDiff_apply ℝ (fun _ : σ ↦ ℝ) i)

theorem contDiff_velocity (P : MvPolynomial (Fin 2) ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (velocity P) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · simpa [velocity] using contDiff_eval (pderiv 1 P) n
  · simpa [velocity] using (contDiff_eval (pderiv 0 P) n).neg

end PaperP1.PolynomialVelocitySmooth
