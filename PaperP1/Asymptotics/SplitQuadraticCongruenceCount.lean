module

public import PaperP1.Diophantine.SplitQuadraticCongruences
public import PaperP1.Arithmetic.DivisorSubpolynomial
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Uniform polynomial-modulus quadratic congruence counts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitQuadraticCongruenceCount

open Filter

theorem polylog_le_rpow (D A₀ ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, D * (Real.log N) ^ A₀ ≤ (N : ℝ) ^ ε := by
  have hlim := ((isLittleO_log_rpow_rpow_atTop A₀ hε).const_mul_left D).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hlim.bound (by norm_num : (0 : ℝ) < 1))
  refine ⟨N₀, ?_⟩
  intro N hN
  have hb : |D * (Real.log N) ^ A₀| ≤ (N : ℝ) ^ ε := by
    simpa only [Function.comp_def, Real.norm_eq_abs, one_mul,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)] using hN₀ N hN
  exact (le_abs_self _).trans hb

theorem uniform_root_count (K : ℕ) (D A₀ ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M X h : ℕ, 0 < M → 0 < h → M ≤ N ^ K →
      (h : ℝ) ≤ D * (Real.log N) ^ A₀ → ∀ S : Finset ℕ,
        (∀ n ∈ S, 0 < n ∧ n ≤ X) → (∀ n ∈ S, M ∣ n * (n + h)) →
          (S.card : ℝ) ≤ (N : ℝ) ^ ε * ((X : ℝ) / M + 1) := by
  obtain ⟨Nd, hNd⟩ := PaperP1.DivisorSubpolynomial.card_divisors_le_rpow_eventually K (ε / 2) (by positivity)
  obtain ⟨Nh, hNh⟩ := polylog_le_rpow D A₀ (ε / 2) (by positivity)
  refine ⟨max 1 (max Nd Nh), ?_⟩
  intro N hN M X h hM hh hMN hshift S hbox hroot
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hd := hNd N (by omega) M hMN
  have hhr := hshift.trans (hNh N (by omega))
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hfactor : (M.divisors.card : ℝ) * h ≤ (N : ℝ) ^ ε := by
    calc
      _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) :=
        mul_le_mul hd hhr (Nat.cast_nonneg h) (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  calc
    (S.card : ℝ) ≤ (M.divisors.card : ℝ) * ((X : ℝ) / M * h + 1) :=
      PaperP1.SplitQuadraticCongruences.root_count M X h hM hh S hbox hroot
    _ ≤ (M.divisors.card : ℝ) * ((h : ℝ) * ((X : ℝ) / M + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      nlinarith only [hh1]
    _ = ((M.divisors.card : ℝ) * h) * ((X : ℝ) / M + 1) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (by positivity)

end PaperP1.SplitQuadraticCongruenceCount
