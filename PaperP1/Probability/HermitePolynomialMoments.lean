module

public import PaperP1.Probability.CompoundPoissonExponential

/-! # All fixed polynomial moments of bounded positive Hermite references -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HermitePolynomialMoments

theorem power_le_exp (r k : ℕ) :
    (1 + (k : ℝ)) ^ r ≤ (r.factorial : ℝ) * Real.exp 1 * Real.exp k := by
  have hh := Real.pow_div_factorial_le_exp (1 + (k : ℝ)) (by positivity) r
  have hfact : 0 < (r.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos r
  have hp := (div_le_iff₀ hfact).mp hh
  rw [Real.exp_add] at hp
  nlinarith only [hp]

theorem uniform_bound (M : ℝ) (r : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ μ α : ℝ, ∀ (hα : 0 ≤ α) (hαμ : α ≤ μ), μ ≤ M →
      Summable (fun k : ℕ ↦ AtomicProbability.realMass
        (HermiteReference.law μ α hα hαμ) k * (1 + (k : ℝ)) ^ r) ∧
      (∑' k : ℕ, AtomicProbability.realMass
        (HermiteReference.law μ α hα hαμ) k * (1 + (k : ℝ)) ^ r) ≤ B := by
  let A : ℝ := (r.factorial : ℝ) * Real.exp 1
  let B : ℝ := A * Real.exp (M * (Real.exp 1 - 1) + M * (Real.exp 1 - 1) ^ 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro μ α hα hαμ hμM
  let a := fun k : ℕ ↦ AtomicProbability.realMass (HermiteReference.law μ α hα hαμ) k
  have ha (k : ℕ) : 0 ≤ a k := AtomicProbability.realMass_nonneg _ _
  have he := CompoundPoissonExponential.hasSum_hermite_exp μ α 1 hα hαμ
  simp only [one_mul] at he
  have hdom (k : ℕ) : a k * (1 + (k : ℝ)) ^ r ≤ A * (a k * Real.exp k) := by
    have hh := mul_le_mul_of_nonneg_left (power_le_exp r k) (ha k)
    dsimp only [A]
    nlinarith only [hh]
  have hs : Summable (fun k : ℕ ↦ a k * (1 + (k : ℝ)) ^ r) :=
    Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (ha k) (by positivity))
      hdom (he.summable.mul_left A)
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' k, A * (a k * Real.exp k) := hs.tsum_le_tsum hdom (he.summable.mul_left A)
    _ = A * Real.exp (μ * (Real.exp 1 - 1) + (α / 2) * (Real.exp 1 - 1) ^ 2) := by
      rw [tsum_mul_left, he.tsum_eq]
    _ ≤ B := by
      apply mul_le_mul_of_nonneg_left ?_ hA
      apply Real.exp_le_exp.mpr
      have hbase : 0 ≤ Real.exp 1 - 1 := by
        have hh := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
        linarith only [hh]
      have hαM : α / 2 ≤ M := by linarith only [hα, hαμ, hμM]
      exact add_le_add (mul_le_mul_of_nonneg_right hμM hbase)
        (mul_le_mul_of_nonneg_right hαM (sq_nonneg _))

end PaperP1.HermitePolynomialMoments
