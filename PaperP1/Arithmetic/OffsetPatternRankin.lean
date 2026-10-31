module

public import PaperP1.Arithmetic.OffsetFactorSupports
public import PaperP1.Arithmetic.PrimePowerTail

/-! # Weighted offset-pattern counts for prime and distinct integer factors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetPatternRankin

open Finset PaperP1.OffsetFactorSupports PaperP1.FiniteEulerRankin

def exponent (c : ℝ) (d : ℕ) (ζ : ℝ) : ℝ := 1 + ((d : ℝ) - 1 + ζ) / c

def primeConstant (c D₀ : ℝ) (d : ℕ) : ℝ :=
  D₀ ^ d * PaperP1.PrimePowerTail.constant (exponent c d 0) / c

def integerConstant (c D₀ : ℝ) (d : ℕ) (ζ : ℝ) : ℝ :=
  D₀ ^ d * PaperP1.PowerSeriesTail.constant (exponent c d ζ)

theorem exponent_gt_one (c : ℝ) (hc : 0 < c) (d : ℕ) (hd : 2 ≤ d)
    (ζ : ℝ) (hζ : 0 ≤ ζ) : 1 < exponent c d ζ := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold exponent
  exact lt_add_of_pos_right 1 (div_pos (by linarith) hc)

theorem primeConstant_pos (c D₀ : ℝ) (hc : 0 < c) (hD₀ : 0 < D₀) (d : ℕ) (hd : 2 ≤ d) :
    0 < primeConstant c D₀ d := by
  exact div_pos (mul_pos (pow_pos hD₀ _) (PaperP1.PrimePowerTail.constant_pos _
    (exponent_gt_one c hc d hd 0 le_rfl))) hc

theorem integerConstant_pos (c D₀ : ℝ) (hc : 0 < c) (hD₀ : 0 < D₀) (d : ℕ) (hd : 2 ≤ d)
    (ζ : ℝ) (hζ : 0 ≤ ζ) : 0 < integerConstant c D₀ d ζ := by
  exact mul_pos (pow_pos hD₀ _) (PaperP1.PowerSeriesTail.constant_pos _
    (exponent_gt_one c hc d hd ζ hζ))

theorem roughWeightedCount_le_exp (Y X a s : ℝ) (hY : 1 < Y) (hX : 0 ≤ X)
    (ha : 0 ≤ a) (hs : 1 < s) :
    roughWeightedCount Y X a ≤ X ^ s *
      Real.exp (a * PaperP1.PrimePowerTail.constant s * Y ^ (1 - s) / Real.log Y) := by
  have hP : ∀ p ∈ primePool Y X, Nat.Prime p ∧ Y < (p : ℝ) := by
    intro p hp
    obtain ⟨hp, _, hcut⟩ := mem_primePool.mp hp
    exact ⟨hp, hcut⟩
  calc
    _ ≤ weightedCount (primePool Y X) X a := roughWeightedCount_le_supports Y X a hX ha
    _ ≤ X ^ s * Real.exp (a * ∑ p ∈ primePool Y X, (p : ℝ) ^ (-s)) :=
      weightedCount_le_exp _ X a s (fun p hp ↦ (hP p hp).1.pos) hX ha (by linarith)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hX s)
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left
        (PaperP1.PrimePowerTail.finite_prime_tail_le _ s Y hs hY hP) ha
      simpa only [mul_div_assoc, mul_assoc] using h

theorem integerWeightedCount_le_exp (Y X a s : ℝ) (hY : 1 ≤ Y) (hX : 0 ≤ X)
    (ha : 0 ≤ a) (hs : 1 < s) :
    integerWeightedCount Y X a ≤ X ^ s *
      Real.exp (a * PaperP1.PowerSeriesTail.constant s * Y ^ (1 - s)) := by
  have hP : ∀ n ∈ integerPool Y X, 1 ≤ n := fun n hn ↦ (mem_integerPool.mp hn).1
  have hrough : ∀ n ∈ integerPool Y X, Y < (n : ℝ) := fun n hn ↦ (mem_integerPool.mp hn).2.2
  calc
    _ ≤ X ^ s * Real.exp (a * ∑ n ∈ integerPool Y X, (n : ℝ) ^ (-s)) :=
      weightedCount_le_exp _ X a s hP hX ha (by linarith)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hX s)
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left
        (PaperP1.ClippedPowerSum.finite_tail_le_power _ s Y hs hY hrough) ha
      simpa only [mul_assoc] using h

theorem coefficient_power (c D₀ B : ℝ) (hc : 0 < c) (hB : 0 < B) (d : ℕ) (ζ : ℝ) :
    (D₀ * B) ^ d * (B ^ c) ^ (1 - exponent c d ζ) = D₀ ^ d * B ^ (1 - ζ) := by
  have hexp : (d : ℝ) + c * (1 - exponent c d ζ) = 1 - ζ := by
    unfold exponent
    field_simp
    ring
  rw [mul_pow, ← Real.rpow_mul hB.le, ← Real.rpow_natCast B d,
    mul_assoc, ← Real.rpow_add hB, hexp]

theorem prime_cost_identity (c D₀ B : ℝ) (hc : 0 < c) (hB : 1 < B) (d : ℕ) :
    (D₀ * B) ^ d * PaperP1.PrimePowerTail.constant (exponent c d 0) *
      (B ^ c) ^ (1 - exponent c d 0) / Real.log (B ^ c) =
        primeConstant c D₀ d * B / Real.log B := by
  have hBpos : 0 < B := by linarith
  have hcoeff := coefficient_power c D₀ B hc hBpos d 0
  rw [sub_zero, Real.rpow_one] at hcoeff
  calc
    _ = PaperP1.PrimePowerTail.constant (exponent c d 0) *
        ((D₀ * B) ^ d * (B ^ c) ^ (1 - exponent c d 0)) / (c * Real.log B) := by
      rw [Real.log_rpow hBpos c]
      ring
    _ = PaperP1.PrimePowerTail.constant (exponent c d 0) * (D₀ ^ d * B) / (c * Real.log B) := by rw [hcoeff]
    _ = _ := by
      unfold primeConstant
      field_simp

theorem integer_cost_identity (c D₀ B : ℝ) (hc : 0 < c) (hB : 0 < B) (d : ℕ) (ζ : ℝ) :
    (D₀ * B) ^ d * PaperP1.PowerSeriesTail.constant (exponent c d ζ) *
      (B ^ c) ^ (1 - exponent c d ζ) = integerConstant c D₀ d ζ * B ^ (1 - ζ) := by
  calc
    _ = PaperP1.PowerSeriesTail.constant (exponent c d ζ) *
        ((D₀ * B) ^ d * (B ^ c) ^ (1 - exponent c d ζ)) := by ring
    _ = _ := by rw [coefficient_power c D₀ B hc hB d ζ]; unfold integerConstant; ring

theorem prime_patterns_explicit (c D₀ : ℝ) (hc : 0 < c) (hD₀ : 0 < D₀)
    (d : ℕ) (hd : 2 ≤ d) (B X : ℝ) (hB : 2 ≤ B) (hX : 1 ≤ X) :
    roughWeightedCount (B ^ c) X ((D₀ * B) ^ d) ≤
      X ^ (exponent c d 0) * Real.exp (primeConstant c D₀ d * B / Real.log B) := by
  have hB1 : 1 < B := by linarith
  have h := roughWeightedCount_le_exp (B ^ c) X ((D₀ * B) ^ d) (exponent c d 0)
    (Real.one_lt_rpow hB1 hc) (by linarith) (by positivity) (exponent_gt_one c hc d hd 0 le_rfl)
  simpa only [prime_cost_identity c D₀ B hc hB1 d] using h

theorem integer_patterns_explicit (c D₀ : ℝ) (hc : 0 < c) (hD₀ : 0 < D₀)
    (d : ℕ) (hd : 2 ≤ d) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (B X : ℝ) (hB : 2 ≤ B) (hX : 1 ≤ X) :
    integerWeightedCount (B ^ c) X ((D₀ * B) ^ d) ≤
      X ^ (exponent c d ζ) * Real.exp (integerConstant c D₀ d ζ * B ^ (1 - ζ)) := by
  have hBpos : 0 < B := by linarith
  have h := integerWeightedCount_le_exp (B ^ c) X ((D₀ * B) ^ d) (exponent c d ζ)
    (Real.one_lt_rpow (by linarith) hc).le (by linarith) (by positivity) (exponent_gt_one c hc d hd ζ hζ)
  simpa only [integer_cost_identity c D₀ B hc hBpos d ζ] using h

theorem prime_patterns_uniform (c D₀ : ℝ) (hc : 0 < c) (hD₀ : 0 < D₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ d : ℕ, d = 2 ∨ d = 3 →
      ∀ B X : ℝ, 2 ≤ B → 1 ≤ X →
        roughWeightedCount (B ^ c) X ((D₀ * B) ^ d) ≤
          X ^ (exponent c d 0) * Real.exp (K * B / Real.log B) := by
  let K := max (primeConstant c D₀ 2) (primeConstant c D₀ 3)
  refine ⟨K, (primeConstant_pos c D₀ hc hD₀ 2 le_rfl).trans_le (le_max_left _ _), ?_⟩
  intro d hd B X hB hX
  have hd2 : 2 ≤ d := by rcases hd with rfl | rfl <;> omega
  have hK : primeConstant c D₀ d ≤ K := by
    rcases hd with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  calc
    _ ≤ X ^ (exponent c d 0) * Real.exp (primeConstant c D₀ d * B / Real.log B) :=
      prime_patterns_explicit c D₀ hc hD₀ d hd2 B X hB hX
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hK (by linarith))
        (Real.log_nonneg (by linarith)))) (Real.rpow_nonneg (by linarith) _)

theorem integer_patterns (c D₀ : ℝ) (hc : 0 < c) (hD₀ : 0 < D₀)
    (d : ℕ) (hd : 2 ≤ d) (ζ : ℝ) (hζ : 0 ≤ ζ) :
    ∃ K : ℝ, 0 < K ∧ ∀ B X : ℝ, 2 ≤ B → 1 ≤ X →
      integerWeightedCount (B ^ c) X ((D₀ * B) ^ d) ≤
        X ^ (exponent c d ζ) * Real.exp (K * B ^ (1 - ζ)) := by
  exact ⟨integerConstant c D₀ d ζ, integerConstant_pos c D₀ hc hD₀ d hd ζ hζ,
    fun B X hB hX ↦ integer_patterns_explicit c D₀ hc hD₀ d hd ζ hζ B X hB hX⟩

/-- Both source sums, with a single prime constant before the choice d=2 or d=3. -/
theorem companion_T21_3 (c D₀ : ℝ) (hc : 0 < c) (hD₀ : 0 < D₀) :
    (∃ K : ℝ, 0 < K ∧ ∀ d : ℕ, d = 2 ∨ d = 3 →
      ∀ B X : ℝ, 2 ≤ B → 1 ≤ X →
        roughWeightedCount (B ^ c) X ((D₀ * B) ^ d) ≤
          X ^ (exponent c d 0) * Real.exp (K * B / Real.log B)) ∧
    (∀ d : ℕ, d = 2 ∨ d = 3 → ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
      ∃ K : ℝ, 0 < K ∧ ∀ B X : ℝ, 2 ≤ B → 1 ≤ X →
        integerWeightedCount (B ^ c) X ((D₀ * B) ^ d) ≤
          X ^ (exponent c d ζ) * Real.exp (K * B ^ (1 - ζ))) := by
  refine ⟨prime_patterns_uniform c D₀ hc hD₀, ?_⟩
  intro d hd ζ hζ _hζ1
  have hd2 : 2 ≤ d := by rcases hd with rfl | rfl <;> omega
  exact integer_patterns c D₀ hc hD₀ d hd2 ζ hζ.le

end PaperP1.OffsetPatternRankin
