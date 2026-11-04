module

public import PaperP1.Analysis.ReducedDyadicScales
public import PaperP1.Asymptotics.SplitQuadraticCongruenceCount

/-! # The literal effective integer parameter after dividing the source equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReducedSourceParameter

def effective (N s : ℕ) : ℝ := (N : ℝ) / s

def parameter (N s : ℕ) : ℕ := ⌈effective N s⌉₊

theorem effective_positive (N s : ℕ) (hN : 0 < N) (hs : 0 < s) : 0 < effective N s :=
  div_pos (by exact_mod_cast hN) (by exact_mod_cast hs)

theorem effective_le_parameter (N s : ℕ) : effective N s ≤ (parameter N s : ℝ) := Nat.le_ceil _

theorem parameter_positive (N s : ℕ) (hN : 0 < N) (hs : 0 < s) : 1 ≤ parameter N s :=
  Nat.one_le_ceil_iff.mpr (effective_positive N s hN hs)

theorem parameter_upper (N s : ℕ) (h : 1 ≤ effective N s) : (parameter N s : ℝ) ≤ 2 * effective N s := by
  have ht := Nat.ceil_lt_add_one (by linarith : 0 ≤ effective N s)
  change (⌈effective N s⌉₊ : ℝ) ≤ _
  linarith

theorem parameter_le_original (N s : ℕ) (hs : 0 < s) : parameter N s ≤ N := by
  apply Nat.ceil_le.mpr
  unfold effective
  have hsp : (0 : ℝ) < s := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  apply (div_le_iff₀ hsp).mpr
  have ht := mul_le_mul_of_nonneg_left hs1 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  simpa only [mul_one] using ht

theorem effective_ge_quotient (N s h : ℕ) (hs : 0 < s) (hsh : s ≤ h) :
    (N : ℝ) / h ≤ effective N s :=
  div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by exact_mod_cast hs) (by exact_mod_cast hsh)

theorem effective_ge_sqrt (N s h : ℕ) (hs : 0 < s) (hsh : s ≤ h) (hh : (h : ℝ) ≤ Real.sqrt N) :
    Real.sqrt N ≤ effective N s := by
  have hsp : (0 : ℝ) < s := by exact_mod_cast hs
  have hsr : (s : ℝ) ≤ Real.sqrt N := (by exact_mod_cast hsh : (s : ℝ) ≤ h).trans hh
  apply (le_div_iff₀ hsp).mpr
  have ht := mul_le_mul_of_nonneg_left hsr (Real.sqrt_nonneg (N : ℝ))
  simpa only [Real.mul_self_sqrt (Nat.cast_nonneg N)] using ht

theorem parameter_ge_sqrt (N s h : ℕ) (hs : 0 < s) (hsh : s ≤ h) (hh : (h : ℝ) ≤ Real.sqrt N) :
    Real.sqrt N ≤ (parameter N s : ℝ) :=
  (effective_ge_sqrt N s h hs hsh hh).trans (effective_le_parameter N s)

theorem log_effective (N s : ℕ) (hN : 0 < N) (hs : 0 < s) :
    Real.log (effective N s) = Real.log N - Real.log s :=
  Real.log_div (by exact_mod_cast hN.ne') (by exact_mod_cast hs.ne')

theorem parameter_log_lower (N s h : ℕ) (hN : 0 < N) (hs : 0 < s) (hsh : s ≤ h)
    (hh : (h : ℝ) ≤ Real.sqrt N) : Real.log N / 2 ≤ Real.log (parameter N s) := by
  have hnR : (0 : ℝ) < N := by exact_mod_cast hN
  have ht := Real.log_le_log (Real.sqrt_pos.mpr hnR) (parameter_ge_sqrt N s h hs hsh hh)
  simpa only [Real.log_sqrt hnR.le] using ht

theorem parameter_log_upper (N s : ℕ) (hN : 0 < N) (hs : 0 < s) :
    Real.log (parameter N s) ≤ Real.log N := by
  have hp : (0 : ℝ) < parameter N s := by exact_mod_cast (show 0 < parameter N s by have := parameter_positive N s hN hs; omega)
  exact Real.log_le_log hp (by exact_mod_cast parameter_le_original N s hs)

theorem log_parameter_gap (N s : ℕ) (hN : 0 < N) (hs : 0 < s) :
    Real.log N - Real.log (parameter N s) ≤ Real.log s := by
  have ht := Real.log_le_log (effective_positive N s hN hs) (effective_le_parameter N s)
  rw [log_effective N s hN hs] at ht
  linarith

theorem parameter_sufficiently_large (L N s h : ℕ) (hL : L ^ 2 ≤ N) (hs : 0 < s) (hsh : s ≤ h)
    (hh : (h : ℝ) ≤ Real.sqrt N) : L ≤ parameter N s := by
  have hLR : (L : ℝ) ≤ Real.sqrt N := by
    have hsqrt := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have hLN : (L : ℝ) ^ 2 ≤ N := by exact_mod_cast hL
    have hroot := Real.sqrt_nonneg (N : ℝ)
    have hL0 := Nat.cast_nonneg L (α := ℝ)
    nlinarith
  exact_mod_cast hLR.trans (parameter_ge_sqrt N s h hs hsh hh)

theorem uniform_parameter_threshold (K A : ℝ) (L : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ s h : ℕ, 0 < s → s ≤ h → (h : ℝ) ≤ K * (Real.log N) ^ A →
      L ≤ parameter N s ∧ parameter N s ≤ N ∧ 1 ≤ parameter N s ∧
        Real.log N / 2 ≤ Real.log (parameter N s) ∧ Real.log (parameter N s) ≤ Real.log N := by
  obtain ⟨Nh, hNh⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow K A (1 / 2) (by norm_num)
  refine ⟨max 1 (max (L ^ 2) Nh), ?_⟩
  intro N hN s h hs hsh hshift
  have hn : 0 < N := by omega
  have hbound : (h : ℝ) ≤ Real.sqrt N := by
    simpa only [Real.sqrt_eq_rpow] using hshift.trans (hNh N (by omega))
  exact ⟨parameter_sufficiently_large L N s h (by omega) hs hsh hbound, parameter_le_original N s hs,
    parameter_positive N s hn hs, parameter_log_lower N s h hn hs hsh hbound, parameter_log_upper N s hn hs⟩

end PaperP1.ReducedSourceParameter
