module

public import PaperP1.Probability.PoissonSequence
public import Mathlib.Tactic.Linarith

/-! # Finite Poisson balance and the two tail factors for Stein solutions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PoissonPartialSums

open Finset PaperP1.PoissonSequence

def cdf (μ : ℝ) (k : ℕ) : ℝ := ∑ i ∈ range (k + 1), mass μ i

def tail (μ : ℝ) (k : ℕ) : ℝ := ∑' i : ℕ, mass μ (i + (k + 1))

theorem mass_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) : 0 ≤ mass μ k := by
  unfold mass
  positivity

theorem tail_summable {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) :
    Summable (fun i : ℕ ↦ mass μ (i + (k + 1))) :=
  (summable_nat_add_iff (k + 1)).mpr (hasSum_mass μ hμ).summable

theorem prefix_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) : 0 ≤ cdf μ k :=
  sum_nonneg (fun i _ ↦ mass_nonneg hμ i)

theorem tail_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) : 0 ≤ tail μ k :=
  tsum_nonneg (fun i ↦ mass_nonneg hμ (i + (k + 1)))

theorem prefix_add_tail {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) : cdf μ k + tail μ k = 1 := by
  have h := (hasSum_mass μ hμ).summable.sum_add_tsum_nat_add (k + 1)
  simpa only [cdf, tail, (hasSum_mass μ hμ).tsum_eq] using h

theorem prefix_succ (μ : ℝ) (k : ℕ) : cdf μ (k + 1) = cdf μ k + mass μ (k + 1) := by
  exact sum_range_succ _ (k + 1)

theorem tail_eq_mass_add {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) :
    tail μ k = mass μ (k + 1) + tail μ (k + 1) := by
  have h0 := prefix_add_tail hμ k
  have h1 := prefix_add_tail hμ (k + 1)
  rw [prefix_succ] at h1
  linarith

theorem weighted_prefix (μ : ℝ) (k : ℕ) :
    (∑ i ∈ range (k + 1), (i : ℝ) * mass μ i) = μ * (cdf μ k - mass μ k) := by
  induction k with
  | zero => simp [cdf]
  | succ k ih =>
    rw [sum_range_succ, ih, prefix_succ]
    have h := mass_succ_mul μ k
    push_cast at h ⊢
    nlinarith

theorem weighted_prefix_le {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) :
    (∑ i ∈ range (k + 1), (i : ℝ) * mass μ i) ≤ (k : ℝ) * cdf μ k := by
  rw [cdf, mul_sum]
  apply sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_right _ (mass_nonneg hμ i)
  exact_mod_cast (show i ≤ k by have h := mem_range.mp hi; omega)

theorem prefix_balance_bound {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) :
    (μ - k) * cdf μ k ≤ μ * mass μ k := by
  have h := weighted_prefix_le hμ k
  rw [weighted_prefix] at h
  nlinarith

theorem prefix_forward_bound {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) :
    μ * cdf μ k ≤ (k + 1 : ℝ) * cdf μ (k + 1) := by
  have h := weighted_prefix_le hμ (k + 1)
  rw [weighted_prefix, prefix_succ] at h
  rw [prefix_succ]
  push_cast at h
  nlinarith

theorem tail_forward_bound {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) :
    (k + 2 : ℝ) * tail μ (k + 1) ≤ μ * tail μ k := by
  have hleft := (tail_summable hμ (k + 1)).mul_left (k + 2 : ℝ)
  have hright := (tail_summable hμ k).mul_left μ
  have h := hleft.tsum_le_tsum (g := fun i ↦ μ * mass μ (i + (k + 1))) ?_ hright
  · simpa only [tail, tsum_mul_left] using h
  · intro i
    have hrec := mass_succ_mul μ (i + (k + 1))
    push_cast at hrec
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hm := mass_nonneg hμ (i + (k + 1) + 1)
    have hprod := mul_nonneg hi hm
    simpa only [Nat.add_assoc] using (show (k + 2 : ℝ) * mass μ (i + (k + 1) + 1) ≤
      μ * mass μ (i + (k + 1)) by nlinarith)

theorem tail_balance_bound {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) :
    (k + 1 - μ : ℝ) * tail μ k ≤ μ * mass μ k := by
  have hforward := tail_forward_bound hμ k
  have htail := tail_nonneg hμ (k + 1)
  have hsplit := tail_eq_mass_add hμ k
  have hrec := mass_succ_mul μ k
  push_cast at hrec
  nlinarith

theorem prefix_mul_tail_bound {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) :
    cdf μ k * tail μ k ≤ μ * mass μ k := by
  have hsum := prefix_add_tail hμ k
  have hp := prefix_nonneg hμ k
  have ht := tail_nonneg hμ k
  by_cases hsplit : cdf μ k ≤ (k + 1 - μ : ℝ)
  · exact (mul_le_mul_of_nonneg_right hsplit ht).trans (tail_balance_bound hμ k)
  · have htail : tail μ k ≤ μ - k := by linarith
    exact (mul_le_mul_of_nonneg_left htail hp).trans (by simpa only [mul_comm] using prefix_balance_bound hμ k)

def lowerFactor (μ : ℝ) (k : ℕ) : ℝ := cdf μ k / (μ * mass μ k)

def upperFactor (μ : ℝ) (k : ℕ) : ℝ := tail μ k / (μ * mass μ k)

theorem lowerFactor_nonneg {μ : ℝ} (hμ : 0 < μ) (k : ℕ) : 0 ≤ lowerFactor μ k :=
  div_nonneg (prefix_nonneg hμ.le k) (mul_nonneg hμ.le (mass_nonneg hμ.le k))

theorem upperFactor_nonneg {μ : ℝ} (hμ : 0 < μ) (k : ℕ) : 0 ≤ upperFactor μ k :=
  div_nonneg (tail_nonneg hμ.le k) (mul_nonneg hμ.le (mass_nonneg hμ.le k))

theorem lowerFactor_mono {μ : ℝ} (hμ : 0 < μ) (k : ℕ) : lowerFactor μ k ≤ lowerFactor μ (k + 1) := by
  have h0 := mass_pos μ hμ k
  have h1 := mass_pos μ hμ (k + 1)
  have hrec := mass_succ_mul μ k
  have hprefix := prefix_forward_bound hμ.le k
  unfold lowerFactor
  apply (div_le_div_iff₀ (mul_pos hμ h0) (mul_pos hμ h1)).mpr
  have hmul := mul_le_mul_of_nonneg_right hprefix h1.le
  push_cast at hrec
  have hrec' := congrArg (fun z : ℝ ↦ cdf μ (k + 1) * z) hrec
  nlinarith

theorem upperFactor_antitone {μ : ℝ} (hμ : 0 < μ) (k : ℕ) : upperFactor μ (k + 1) ≤ upperFactor μ k := by
  have h0 := mass_pos μ hμ k
  have h1 := mass_pos μ hμ (k + 1)
  have hrec := mass_succ_mul μ k
  have htail := tail_forward_bound hμ.le k
  have ht := tail_nonneg hμ.le (k + 1)
  unfold upperFactor
  apply (div_le_div_iff₀ (mul_pos hμ h1) (mul_pos hμ h0)).mpr
  have hmul := mul_le_mul_of_nonneg_right (show (k + 1 : ℝ) * tail μ (k + 1) ≤ μ * tail μ k by linarith) h1.le
  push_cast at hrec
  nlinarith

theorem adjacent_factor_bound {μ : ℝ} (hμ : 0 < μ) (k : ℕ) :
    (upperFactor μ (k + 1) + lowerFactor μ k) * mass μ (k + 1) ≤ 1 := by
  have h0 := mass_pos μ hμ k
  have h1 := mass_pos μ hμ (k + 1)
  have hrec := mass_succ_mul μ k
  push_cast at hrec
  have htail := tail_forward_bound hμ.le k
  have ht := tail_nonneg hμ.le (k + 1)
  have hsum := prefix_add_tail hμ.le k
  have hp := prefix_nonneg hμ.le k
  have hid : (upperFactor μ (k + 1) + lowerFactor μ k) * mass μ (k + 1) =
      tail μ (k + 1) / μ + cdf μ k / (k + 1 : ℝ) := by
    unfold upperFactor lowerFactor
    field_simp
    nlinarith
  rw [hid]
  have ht' : tail μ (k + 1) / μ ≤ tail μ k / (k + 1 : ℝ) := by
    apply (div_le_div_iff₀ hμ (by positivity : (0 : ℝ) < k + 1)).mpr
    nlinarith
  calc
    _ ≤ tail μ k / (k + 1 : ℝ) + cdf μ k / (k + 1 : ℝ) := add_le_add ht' le_rfl
    _ = 1 / (k + 1 : ℝ) := by rw [← add_div]; congr 1; linarith
    _ ≤ 1 := (div_le_one (by positivity : (0 : ℝ) < k + 1)).mpr (by have h := Nat.cast_nonneg (α := ℝ) k; linarith)

end PaperP1.PoissonPartialSums
