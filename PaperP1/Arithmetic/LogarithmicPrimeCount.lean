module

public import PaperP1.Arithmetic.ChebyshevPrimeCount
public import PaperP1.Asymptotics.ExpSqrtLog
public import PaperP1.Asymptotics.UniformReal

@[expose] public section

/-!
# Uniform prime-support counts at logarithmic cutoffs

The elementary finite Chebyshev estimate implies a uniform
O(log N / log log N) prime count for every H ≤ D log N. No lower bound
on H is needed: monotonicity permits a common rounded upper cutoff.
-/

namespace PaperP1.LogarithmicPrimeCount

open DefectCounting

abbrev primeCount (H : ℕ) : ℕ := (smallPrimesUpTo H).card

theorem primeCount_mono {H K : ℕ} (hHK : H ≤ K) :
    primeCount H ≤ primeCount K := by
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hpp, hpH⟩ := mem_smallPrimesUpTo.mp hp
  exact mem_smallPrimesUpTo.mpr ⟨hpp, hpH.trans hHK⟩

theorem log_mul_primeCount_le {H : ℕ} (hH : 4 ≤ H) :
    (primeCount H : ℝ) * Real.log H ≤ 14 * Real.log 2 * H := by
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hpow : H < 2 ^ (Nat.log 2 H + 1) := Nat.lt_pow_succ_log_self (by omega) H
  have hpowReal : (H : ℝ) ≤ ((2 ^ (Nat.log 2 H + 1) : ℕ) : ℝ) := by
    exact_mod_cast hpow.le
  have hlogs := Real.log_le_log hHpos hpowReal
  have hlog : Real.log (H : ℝ) ≤ ((Nat.log 2 H : ℝ) + 1) * Real.log 2 := by
    norm_num only [Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat] at hlogs
    exact hlogs
  have hL : 1 ≤ Nat.log 2 H := by
    apply Nat.le_log_of_pow_le (by omega)
    norm_num
    omega
  have hLr : (1 : ℝ) ≤ Nat.log 2 H := by exact_mod_cast hL
  have hlogle : Real.log (H : ℝ) ≤ 2 * (Nat.log 2 H : ℝ) * Real.log 2 :=
    hlog.trans (mul_le_mul_of_nonneg_right (by linarith) hlogTwo.le)
  have hcheb : (Nat.log 2 H : ℝ) * (primeCount H : ℝ) ≤ 7 * (H : ℝ) := by
    exact_mod_cast ChebyshevPrimeCount.log_mul_count_le_seven_mul hH
  calc
    _ ≤ (primeCount H : ℝ) * (2 * (Nat.log 2 H : ℝ) * Real.log 2) :=
      mul_le_mul_of_nonneg_left hlogle (by positivity)
    _ = (2 * Real.log 2) * ((Nat.log 2 H : ℝ) * (primeCount H : ℝ)) := by ring
    _ ≤ (2 * Real.log 2) * (7 * (H : ℝ)) :=
      mul_le_mul_of_nonneg_left hcheb (by positivity)
    _ = 14 * Real.log 2 * H := by ring

/-- Common logarithmic prime-count bound, uniform over all smaller cutoffs. -/
theorem primeCount_le_log_div_loglog
    {N H : ℕ} (D : ℝ) (hD : 0 ≤ D)
    (hlogN : 4 ≤ Real.log (N : ℝ))
    (hH : (H : ℝ) ≤ D * Real.log N) :
    (primeCount H : ℝ) ≤
      (14 * Real.log 2 * (D + 2)) * Real.log N / Real.log (Real.log N) := by
  let M : ℕ := ⌈(D + 1) * Real.log N⌉₊
  have hlogNpos : 0 < Real.log (N : ℝ) := by linarith
  have hloglog : 0 < Real.log (Real.log (N : ℝ)) := Real.log_pos (by linarith)
  have hceil : (D + 1) * Real.log N ≤ (M : ℝ) := Nat.le_ceil _
  have hMlower : Real.log N ≤ (M : ℝ) := by nlinarith
  have hM4 : 4 ≤ M := by exact_mod_cast (hlogN.trans hMlower)
  have hMupper : (M : ℝ) ≤ (D + 2) * Real.log N := by
    have hc : (M : ℝ) < (D + 1) * Real.log N + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    nlinarith
  have hHM : H ≤ M := by
    have hle : (H : ℝ) ≤ M := by nlinarith
    exact_mod_cast hle
  have hcount : (primeCount H : ℝ) ≤ (primeCount M : ℝ) := by
    exact_mod_cast primeCount_mono hHM
  have hlogM : Real.log (Real.log (N : ℝ)) ≤ Real.log (M : ℝ) :=
    Real.log_le_log hlogNpos hMlower
  apply (le_div_iff₀ hloglog).mpr
  calc
    (primeCount H : ℝ) * Real.log (Real.log N) ≤
        (primeCount M : ℝ) * Real.log M :=
      mul_le_mul hcount hlogM hloglog.le (by positivity)
    _ ≤ 14 * Real.log 2 * (M : ℝ) := log_mul_primeCount_le hM4
    _ ≤ 14 * Real.log 2 * ((D + 2) * Real.log N) :=
      mul_le_mul_of_nonneg_left hMupper (by positivity)
    _ = (14 * Real.log 2 * (D + 2)) * Real.log N := by ring

theorem prime_supports_uniformSubpolynomial
    (D : ℝ) (hD : 0 ≤ D) :
    UniformSubpolynomialOn
      (fun N H => (H : ℝ) ≤ D * Real.log N)
      (fun _ H => ((2 ^ primeCount H : ℕ) : ℝ)) := by
  intro k hk
  obtain ⟨Ncore, hcore⟩ :=
    ExpSqrtLog.two_pow_log_div_loglog_pow_le_nat_eventually
      (14 * Real.log 2 * (D + 2)) (by positivity) k hk
  refine ⟨max Ncore (⌈Real.exp 4⌉₊ + 1), ?_⟩
  intro N hN H hH
  have hNlarge : ⌈Real.exp 4⌉₊ + 1 ≤ N := (le_max_right _ _).trans hN
  have hexp : Real.exp 4 ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈Real.exp 4⌉₊ ≤ N by omega))
  have hlog : 4 ≤ Real.log (N : ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 4) hexp
  have hbound := hcore N ((le_max_left _ _).trans hN) (primeCount H)
    (primeCount_le_log_div_loglog D hD hlog hH)
  simpa only [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 ^ primeCount H : ℕ))] using hbound

/-- Actual number of small-prime subsets, with the threshold before H. -/
theorem smooth_support_count_le_rpow_eventually
    (D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H : ℕ,
      (H : ℝ) ≤ D * Real.log N →
      (((smallPrimesUpTo H).powerset.card : ℕ) : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := UniformReal.uniformSubpolynomialOn_le_rpow
    (prime_supports_uniformSubpolynomial D hD) ε hε
  refine ⟨N₀, ?_⟩
  intro N hN H hH
  simpa only [Finset.card_powerset, primeCount,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 ^ (smallPrimesUpTo H).card : ℕ))]
    using hN₀ N hN H hH

end PaperP1.LogarithmicPrimeCount

