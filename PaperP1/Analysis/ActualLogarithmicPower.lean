module

public import PaperP1.Analysis.RecursiveLogarithmicDifferencing
public import PaperP1.Analysis.FixedOrderLogarithmicScale
public import PaperP1.Analysis.RecursiveBudgetPower
public import PaperP1.Analysis.RoundedLogarithmicParameters
public import PaperP1.Analysis.RoundedTerminalDecay

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ActualLogarithmicPower
open Finset Filter PaperP1 FixedOrderLogarithmicScale RoundedLogarithmicParameters
open scoped Classical

def constant (n : ℕ) : ℝ := (6 : ℝ)^(n+1)+(n.factorial : ℝ)+4

def decay (n : ℕ) : ℝ := exponent n/(2 : ℝ)^n

theorem constant_four_le (n : ℕ) : 4 ≤ constant n := by
  have h1 := pow_nonneg (by norm_num : (0 : ℝ) ≤ 6) (n+1)
  have h2 : (0 : ℝ) ≤ n.factorial := Nat.cast_nonneg n.factorial
  unfold constant
  linarith only [h1,h2]

theorem decay_pos (n : ℕ) (hn : 0 < n) : 0 < decay n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold decay exponent
  positivity

theorem envelope_bound (n X : ℕ) (hn : 0 < n) (hX : 1 ≤ X) :
    RoundedTerminalDecay.envelope n X ≤ constant n*(X : ℝ)^(-(exponent n)) := by
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXp : (0 : ℝ) < X := by linarith only [hXR]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hBeta : exponent n ≤ (1/16 : ℝ) := by
    unfold exponent
    exact one_div_le_one_div_of_le (by norm_num) (by linarith only [hn1] : (16 : ℝ) ≤ 16*(n : ℝ))
  have hTerm (c p : ℝ) (hc : 0 ≤ c) (hp : exponent n ≤ p) :
      c/(X : ℝ)^p ≤ c*(X : ℝ)^(-(exponent n)) := by
    have hPow := Real.rpow_le_rpow_of_exponent_le hXR hp
    have hInv := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hXp (exponent n)) hPow
    calc
      _ = c*(1/(X : ℝ)^p) := by ring
      _ ≤ c*(1/(X : ℝ)^(exponent n)) := mul_le_mul_of_nonneg_left hInv hc
      _ = _ := by rw [Real.rpow_neg hXp.le,one_div]
  have hFirst := hTerm ((6 : ℝ)^(n+1)) (1/2) (by positivity) (by linarith only [hBeta])
  have hSecond := hTerm (n.factorial : ℝ) (7/16) (Nat.cast_nonneg _) (by linarith only [hBeta])
  have hNN := Real.rpow_nonneg (Nat.cast_nonneg X) (-(exponent n))
  unfold RoundedTerminalDecay.envelope constant
  nlinarith only [hFirst,hSecond,hNN]

theorem uniform_bound (n : ℕ) (hn : 0 < n) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ t : ℝ,
      (X : ℝ)^(3/4 : ℝ) ≤ |t| → |t| ≤ (X : ℝ)^((n : ℝ)+1/4) →
      ‖∑ j ∈ Ico X (2*X), LogarithmicExponentialSum.function t j‖ ≤ constant n*(X : ℝ)^(1-decay n) := by
  obtain ⟨NB,hNB,hBound⟩ := RoundedTerminalDecay.uniform_logarithmic_bound n hn
  obtain ⟨NG,hG⟩ := eventually_atTop.mp (geometry_eventually n hn)
  refine ⟨max NB NG,by omega,?_⟩
  intro X hX t hLower hUpper
  obtain ⟨hX1,hK,hKHalf,hKUpper,hAll⟩ := hG X (by omega)
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hXp : (0 : ℝ) < X := by linarith only [hXR]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hBetaNN : 0 ≤ exponent n := by unfold exponent; positivity
  have hPower := RecursiveBudgetPower.bound (count n X) n X (exponent n) (constant n)
    (RoundedTerminalDecay.envelope n X) hXR hBetaNN (constant_four_le n) hKHalf
    (RoundedTerminalDecay.envelope_nonneg n X) (envelope_bound n X hn hX1)
  have he : -(exponent n)/(2 : ℝ)^n=-(decay n) := by unfold decay; ring
  rw [he] at hPower
  have hRaw := hBound X (by omega) t hLower hUpper
  calc
    _ ≤ (X : ℝ)*(constant n*(X : ℝ)^(-(decay n))) :=
      hRaw.trans (mul_le_mul_of_nonneg_left hPower (Nat.cast_nonneg X))
    _ = constant n*((X : ℝ)^(1 : ℝ)*(X : ℝ)^(-(decay n))) := by rw [Real.rpow_one]; ring
    _ = _ := by
      simpa only [sub_eq_add_neg] using congrArg (fun z : ℝ ↦ constant n*z)
        (Real.rpow_add hXp (1 : ℝ) (-(decay n))).symm

theorem relative_bound (n : ℕ) (hn : 0 < n) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ t : ℝ,
      (X : ℝ)^(3/4 : ℝ) ≤ |t| → |t| ≤ (X : ℝ)^((n : ℝ)+1/4) →
      ‖∑ j ∈ Ico X (2*X), LogarithmicExponentialSum.function t j‖/(X : ℝ) ≤ constant n/(X : ℝ)^(decay n) := by
  obtain ⟨X₀,hX₀,hBound⟩ := uniform_bound n hn
  refine ⟨X₀,hX₀,?_⟩
  intro X hX t hLower hUpper
  have hXp : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  calc
    _ ≤ (constant n*(X : ℝ)^(1-decay n))/(X : ℝ) :=
      div_le_div_of_nonneg_right (hBound X hX t hLower hUpper) (Nat.cast_nonneg X)
    _ = _ := by
      rw [Real.rpow_sub hXp,Real.rpow_one]
      field_simp [hXp.ne',(Real.rpow_pos_of_pos hXp (decay n)).ne']
end PaperP1.ActualLogarithmicPower
