module

public import PaperP1.Arithmetic.ShortPrimePassage
public import PaperP1.Asymptotics.ModerateOrder

/-! # A uniform first-passage order with sharp leading coefficient 1/A -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShortCertificateOrder

open Filter

def raw (A K : ℝ) (N : ℕ) : ℝ :=
  (Real.log (K * N) + Real.log (Real.log N)) / (A * Real.log (Real.log N))

def upper (A K : ℝ) (N : ℕ) : ℕ := ⌈raw A K N⌉₊ + 1

def scaled (A K : ℝ) (N : ℕ) : ℝ :=
  (upper A K N : ℝ) * Real.log (Real.log N) / Real.log N

theorem raw_nonneg (A K : ℝ) (N : ℕ) (hA : 0 < A) (hK : 1 ≤ K)
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) : 0 ≤ raw A K N := by
  have hKN : (1 : ℝ) ≤ K * N := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith only [hn, hK]
  dsimp [raw]
  exact div_nonneg (add_nonneg (Real.log_nonneg hKN) (Real.log_nonneg hlog))
    (mul_nonneg hA.le (Real.log_nonneg hlog))

theorem bounds_eventually (A K : ℝ) (hA : 0 < A) (hK : 1 ≤ K) :
    ∀ᶠ N : ℕ in atTop,
      (1 / A) * (Real.log (K * N) / Real.log N + Real.log (Real.log N) / Real.log N) ≤ scaled A K N ∧
      scaled A K N ≤
        (1 / A) * (Real.log (K * N) / Real.log N + Real.log (Real.log N) / Real.log N) +
          2 * (Real.log (Real.log N) / Real.log N) := by
  filter_upwards [PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 2),
    eventually_ge_atTop 1] with N hlog hN
  have hl : 0 < Real.log N := by linarith
  have hll : 0 < Real.log (Real.log N) := Real.log_pos (by linarith)
  have hraw := raw_nonneg A K N hA hK hN (by linarith)
  have hlo : raw A K N ≤ (upper A K N : ℝ) := by
    exact (Nat.le_ceil _).trans (by dsimp [upper]; push_cast; linarith)
  have hhi : (upper A K N : ℝ) ≤ raw A K N + 2 := by
    have hc := (Nat.ceil_lt_add_one hraw).le
    dsimp [upper]
    push_cast
    linarith
  have hidentity : raw A K N * Real.log (Real.log N) / Real.log N =
      (1 / A) * (Real.log (K * N) / Real.log N + Real.log (Real.log N) / Real.log N) := by
    dsimp [raw]
    field_simp
  constructor
  · rw [← hidentity]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hlo hll.le) hl.le
  · calc
      _ ≤ (raw A K N + 2) * Real.log (Real.log N) / Real.log N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hhi hll.le) hl.le
      _ = _ := by rw [add_mul, add_div, hidentity]; ring

theorem scaled_tendsto (A K : ℝ) (hA : 0 < A) (hK : 1 ≤ K) :
    Tendsto (scaled A K) atTop (nhds (1 / A)) := by
  have hlo := ((PaperP1.PrimeLogBudget.log_mul_div_log_tendsto K (by linarith)).add
    PaperP1.ModerateOrder.loglog_div_log_tendsto_zero).const_mul (1 / A)
  have hhi := hlo.add (PaperP1.ModerateOrder.loglog_div_log_tendsto_zero.const_mul 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [add_zero, mul_one] using hlo) (by simpa only [mul_zero, add_zero, mul_one] using hhi)
  · exact (bounds_eventually A K hA hK).mono fun _ h ↦ h.1
  · exact (bounds_eventually A K hA hK).mono fun _ h ↦ h.2

theorem upper_div_log_tendsto (A K : ℝ) (hA : 0 < A) (hK : 1 ≤ K) :
    Tendsto (fun N : ℕ ↦ (upper A K N : ℝ) / Real.log N) atTop (nhds 0) := by
  have hinv := tendsto_inv_atTop_zero.comp PaperP1.ModerateOrder.loglog_tendsto_atTop
  have hlim := (scaled_tendsto A K hA hK).mul hinv
  have heq : (fun N : ℕ ↦ scaled A K N * (Real.log (Real.log N))⁻¹) =ᶠ[atTop]
      (fun N : ℕ ↦ (upper A K N : ℝ) / Real.log N) := by
    filter_upwards [PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 2)] with N hlog
    have hll : 0 < Real.log (Real.log N) := Real.log_pos (by linarith)
    dsimp [scaled]
    field_simp
  exact Tendsto.congr' heq (by simpa only [mul_zero, Function.comp_def] using hlim)

theorem passage_le_upper (A K : ℝ) (N Z : ℕ) (hA : 0 < A) (hK : 1 ≤ K)
    (hN : 1 ≤ N) (hlog : 2 ≤ Real.log N) (hZ : 0 < Z)
    (hheight : (Z : ℝ) ≤ K * N * Real.log N) :
    PaperP1.ShortPrimePassage.order Z ((Real.log N) ^ A) ≤ upper A K N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log N := by linarith
  have hll : 0 < Real.log (Real.log N) := Real.log_pos (by linarith)
  have hlogZ : Real.log (Z : ℝ) ≤ Real.log (K * N) + Real.log (Real.log N) := by
    have h := Real.log_le_log (by exact_mod_cast hZ) hheight
    rwa [Real.log_mul (by positivity : K * N ≠ 0) hl.ne'] at h
  have hratio : Real.log (Z : ℝ) / Real.log ((Real.log N) ^ A) ≤ raw A K N := by
    rw [Real.log_rpow hl]
    exact div_le_div_of_nonneg_right hlogZ (mul_nonneg hA.le hll.le)
  have hfloor : ⌊Real.log (Z : ℝ) / Real.log ((Real.log N) ^ A)⌋₊ ≤ ⌈raw A K N⌉₊ :=
    (Nat.floor_mono hratio).trans (Nat.floor_le_ceil _)
  simpa only [PaperP1.ShortPrimePassage.order, upper] using Nat.add_le_add_right hfloor 1

end PaperP1.ShortCertificateOrder
