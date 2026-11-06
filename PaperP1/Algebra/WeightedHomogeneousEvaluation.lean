module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic.Ring

/-! # Exact weighted homogeneous scaling for actual algebra evaluations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedHomogeneousEvaluation

open MvPolynomial

theorem aeval_scale {F A σ : Type*} [CommSemiring F] [CommSemiring A] [Algebra F A]
    (w : σ → ℕ) {e : ℕ} (p : MvPolynomial σ F) (hp : p.IsWeightedHomogeneous w e)
    (t : A) (v : σ → A) :
    aeval (R := F) (fun i ↦ t ^ (w i) * v i) p = t ^ e * aeval (R := F) v p := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simp only [map_zero, mul_zero]
  | add p q _hp _hq ihp ihq => rw [map_add, map_add, ihp, ihq, mul_add]
  | monomial d c hd =>
    have hd' : ∑ i ∈ d.support, w i * d i = e := by
      simpa only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Nat.mul_comm] using hd
    have ht : d.prod (fun i k ↦ (t ^ (w i)) ^ k) = t ^ e := by
      rw [Finsupp.prod]
      simp_rw [← pow_mul]
      rw [Finset.prod_pow_eq_pow_sum, hd']
    simp only [aeval_monomial, mul_pow, Finsupp.prod_mul, ht]
    ring

theorem aeval_homogeneous_scale {F A σ : Type*} [CommSemiring F] [CommSemiring A] [Algebra F A]
    {e : ℕ} (p : MvPolynomial σ F) (hp : p.IsHomogeneous e) (t : A) (v : σ → A) :
    aeval (R := F) (fun i ↦ t * v i) p = t ^ e * aeval (R := F) v p := by
  simpa only [Pi.one_apply, pow_one] using aeval_scale (1 : σ → ℕ) p hp t v

end PaperP1.WeightedHomogeneousEvaluation
