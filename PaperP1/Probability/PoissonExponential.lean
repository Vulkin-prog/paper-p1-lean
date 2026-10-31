module

public import PaperP1.Probability.PoissonSequence
public import PaperP1.Probability.AtomicProbability

/-! # Exact exponential-moment sums for Poisson and its quadratic correction -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PoissonExponential

open PaperP1.PoissonSequence

theorem hasSum_mass_exp (μ t : ℝ) :
    HasSum (fun k : ℕ ↦ mass μ k * Real.exp (t * k)) (Real.exp (μ * (Real.exp t - 1))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (μ * Real.exp t)).mul_left (Real.exp (-μ))
  have hid (k : ℕ) : mass μ k * Real.exp (t * k) =
      Real.exp (-μ) * ((μ * Real.exp t) ^ k / (k.factorial : ℝ)) := by
    rw [mul_comm t (k : ℝ), Real.exp_nat_mul]
    unfold mass
    rw [mul_pow]
    ring
  simp_rw [hid]
  convert h using 1
  rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
  congr 1
  ring

theorem hasSum_shift_exp {a : ℕ → ℝ} {s : ℝ} (t : ℝ)
    (ha : HasSum (fun k : ℕ ↦ a k * Real.exp (t * k)) s) :
    HasSum (fun k : ℕ ↦ shift a k * Real.exp (t * k)) (Real.exp t * s) := by
  have h := hasSum_shift (ha.mul_left (Real.exp t))
  convert h using 1
  funext k
  cases k with
  | zero => simp
  | succ k =>
    simp only [shift_succ, Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.exp_add]
    ring

theorem hasSum_quadraticMass_exp (μ α t : ℝ) :
    HasSum (fun k : ℕ ↦ quadraticMass μ α k * Real.exp (t * k))
      (Real.exp (μ * (Real.exp t - 1)) * (1 + α / 2 * (Real.exp t - 1) ^ 2)) := by
  have hm := hasSum_mass_exp μ t
  have hs := hasSum_shift_exp t hm
  have hss := hasSum_shift_exp t hs
  have hd := (hss.sub (hs.mul_left 2)).add hm
  have h := hm.add (hd.mul_left (α / 2))
  convert h using 1
  · funext k
    unfold quadraticMass secondDifference
    ring
  · ring

theorem descFactorial_le_exp (k j : ℕ) :
    (k.descFactorial j : ℝ) ≤ (j.factorial : ℝ) * Real.exp k := by
  calc
    _ ≤ (k : ℝ) ^ j := by exact_mod_cast Nat.descFactorial_le_pow k j
    _ ≤ _ := by
      have h := Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k) j
      have hf : (0 : ℝ) < j.factorial := by positivity
      have h' := (div_le_iff₀ hf).mp h
      simpa only [mul_comm] using h'

theorem summable_factorial_of_exp {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k)
    (hexp : Summable (fun k : ℕ ↦ a k * Real.exp k)) (j : ℕ) :
    Summable (fun k ↦ a k * (k.descFactorial j : ℝ)) := by
  have hdom := hexp.mul_left (j.factorial : ℝ)
  apply hdom.of_nonneg_of_le (fun k ↦ mul_nonneg (ha k) (Nat.cast_nonneg _))
  intro k
  have h := mul_le_mul_of_nonneg_left (descFactorial_le_exp k j) (ha k)
  simpa only [mul_left_comm, mul_assoc] using h

end PaperP1.PoissonExponential
