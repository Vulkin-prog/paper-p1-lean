module

public import PaperP1.Probability.AtomicSignedLaw
public import Mathlib.Probability.Distributions.Poisson.Basic

/-! # Poisson singleton masses and their finite differences -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PoissonSequence

open MeasureTheory ProbabilityTheory

def mass (μ : ℝ) (k : ℕ) : ℝ := Real.exp (-μ) * μ ^ k / (k.factorial : ℝ)

theorem hasSum_mass (μ : ℝ) (hμ : 0 ≤ μ) : HasSum (mass μ) 1 :=
  hasSum_one_poissonMeasure ⟨μ, hμ⟩

theorem mass_pos (μ : ℝ) (hμ : 0 < μ) (k : ℕ) : 0 < mass μ k := by
  unfold mass
  positivity

def shift (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => a k

@[simp] theorem shift_zero (a : ℕ → ℝ) : shift a 0 = 0 := rfl

@[simp] theorem shift_succ (a : ℕ → ℝ) (k : ℕ) : shift a (k + 1) = a k := rfl

theorem hasSum_shift {a : ℕ → ℝ} {s : ℝ} (ha : HasSum a s) : HasSum (shift a) s := by
  have h : HasSum (fun k ↦ shift a (k + 1)) s := ha
  simpa only [shift_zero, zero_add] using h.zero_add

def secondDifference (a : ℕ → ℝ) (k : ℕ) : ℝ := shift (shift a) k - 2 * shift a k + a k

theorem hasSum_secondDifference {a : ℕ → ℝ} {s : ℝ} (ha : HasSum a s) :
    HasSum (secondDifference a) 0 := by
  have h := ((hasSum_shift (hasSum_shift ha)).sub ((hasSum_shift ha).mul_left 2)).add ha
  have hs : s - 2 * s + s = 0 := by ring
  rw [hs] at h
  exact h

def quadraticMass (μ α : ℝ) (k : ℕ) : ℝ := mass μ k + (α / 2) * secondDifference (mass μ) k

theorem hasSum_quadraticMass (μ α : ℝ) (hμ : 0 ≤ μ) : HasSum (quadraticMass μ α) 1 := by
  have h := (hasSum_mass μ hμ).add ((hasSum_secondDifference (hasSum_mass μ hμ)).mul_left (α / 2))
  convert h using 1
  · funext k
    rfl
  · ring

theorem mass_succ_mul (μ : ℝ) (k : ℕ) :
    mass μ (k + 1) * (k + 1 : ℕ) = μ * mass μ k := by
  unfold mass
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  have hks : (k + 1 : ℝ) ≠ 0 := by positivity
  field_simp

theorem shift_mass (μ : ℝ) (hμ : μ ≠ 0) (k : ℕ) :
    shift (mass μ) k = (k : ℝ) / μ * mass μ k := by
  cases k with
  | zero => simp
  | succ k =>
    rw [shift_succ]
    have h := mass_succ_mul μ k
    push_cast at h ⊢
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hμ).mpr
    nlinarith

theorem secondDifference_mass (μ : ℝ) (hμ : μ ≠ 0) (k : ℕ) :
    secondDifference (mass μ) k = mass μ k / μ ^ 2 * (((k : ℝ) - μ) ^ 2 - k) := by
  have hfirst := shift_mass μ hμ k
  have hsecond : shift (shift (mass μ)) k =
      (k : ℝ) * ((k : ℝ) - 1) / μ ^ 2 * mass μ k := by
    cases k with
    | zero => simp
    | succ k =>
      have hr : mass μ k = (k + 1 : ℕ) / μ * mass μ (k + 1) := by
        simpa only [shift_succ] using shift_mass μ hμ (k + 1)
      rw [shift_succ, shift_mass μ hμ k, hr]
      push_cast
      field_simp
      ring
  change shift (shift (mass μ)) k - 2 * shift (mass μ) k + mass μ k = _
  rw [hfirst, hsecond]
  field_simp
  ring

theorem quadraticMass_formula (μ α : ℝ) (hμ : μ ≠ 0) (k : ℕ) :
    quadraticMass μ α k = mass μ k *
      (1 + α / (2 * μ ^ 2) * (((k : ℝ) - μ) ^ 2 - k)) := by
  change mass μ k + (α / 2) * secondDifference (mass μ) k = _
  rw [secondDifference_mass μ hμ k]
  field_simp

end PaperP1.PoissonSequence
