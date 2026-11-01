module

public import PaperP1.Model.PrimeRunCylinder
public import PaperP1.Arithmetic.SharpPrimeCount
public import Mathlib.Analysis.SpecificLimits.Normed

/-! # The exact dyadic prime subsequence and its prime-cylinder logarithmic cost -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeCylinderScale

open Filter PaperP1.Model PaperP1.LocalDefectBound

def size (q : ℕ) : ℕ := 2 ^ (q - 1)

def cutoff (q : ℕ) : ℕ := dyadicCutoff (size q) (q - 1)

def primeCharge (q : ℕ) : ℝ := Real.log (size q) / size q * (primeCount (cutoff q) : ℝ) * Real.log 2

theorem size_pos (q : ℕ) : 0 < size q := pow_pos (by norm_num) _

theorem index_le_size {q : ℕ} (hq : 1 ≤ q) : q ≤ size q := by
  have h := Nat.lt_two_pow_self (n := q - 1)
  unfold size
  omega

theorem size_cast (q : ℕ) : (size q : ℝ) = (2 : ℝ) ^ (q - 1) := by simp only [size, Nat.cast_pow, Nat.cast_ofNat]

theorem pow_relation {q : ℕ} (hq : 1 ≤ q) : (2 : ℝ) ^ q = 2 * (size q : ℝ) := by
  calc
    _ = (2 : ℝ) ^ ((q - 1) + 1) := congrArg (fun n : ℕ ↦ (2 : ℝ) ^ n) (by omega)
    _ = _ := by rw [pow_succ, size_cast]; ring

theorem log_size (q : ℕ) : Real.log (size q) = (q - 1 : ℕ) * Real.log 2 := by rw [size_cast, Real.log_pow]

theorem size_tendsto : Tendsto size atTop atTop := by
  refine tendsto_atTop.mpr fun k ↦ ?_
  filter_upwards [eventually_ge_atTop (max k 1)] with q hq
  exact (show k ≤ q by omega).trans (index_le_size (by omega))

theorem size_real_tendsto : Tendsto (fun q ↦ (size q : ℝ)) atTop atTop :=
  (tendsto_natCast_atTop_atTop (R := ℝ)).comp size_tendsto

theorem cutoff_tendsto : Tendsto cutoff atTop atTop := by
  refine tendsto_atTop.mpr fun k ↦ ?_
  filter_upwards [size_tendsto.eventually (eventually_ge_atTop k)] with q hq
  dsimp [cutoff, dyadicCutoff]
  omega

theorem index_div_size_tendsto : Tendsto (fun q : ℕ ↦ (q : ℝ) / size q) atTop (nhds 0) := by
  have hbase : Tendsto (fun q : ℕ ↦ (q : ℝ) / (2 : ℝ) ^ q) atTop (nhds 0) := by
    simpa only [pow_one] using tendsto_pow_const_div_const_pow_of_one_lt 1 (r := (2 : ℝ)) (by norm_num)
  have heq : (fun q : ℕ ↦ (q : ℝ) / size q) =ᶠ[atTop] (fun q : ℕ ↦ 2 * ((q : ℝ) / (2 : ℝ) ^ q)) := by
    filter_upwards [eventually_ge_atTop 1] with q hq
    rw [pow_relation hq]
    field_simp
  exact Tendsto.congr' heq.symm (by simpa only [mul_zero] using hbase.const_mul 2)

theorem one_div_size_tendsto : Tendsto (fun q ↦ (1 : ℝ) / size q) atTop (nhds 0) :=
  tendsto_const_nhds.div_atTop size_real_tendsto

theorem log_size_div_size_tendsto : Tendsto (fun q ↦ Real.log (size q) / size q) atTop (nhds 0) := by
  have heq : (fun q ↦ Real.log (size q) / size q) =ᶠ[atTop]
      (fun q : ℕ ↦ ((q : ℝ) / size q - 1 / size q) * Real.log 2) := by
    filter_upwards [eventually_ge_atTop 1] with q hq
    rw [log_size, Nat.cast_sub hq, Nat.cast_one]
    ring
  exact Tendsto.congr' heq.symm (by simpa using (index_div_size_tendsto.sub one_div_size_tendsto).mul_const (Real.log 2))

theorem log_size_tendsto : Tendsto (fun q ↦ Real.log (size q)) atTop atTop :=
  Real.tendsto_log_atTop.comp size_real_tendsto

theorem log_size_div_index_tendsto : Tendsto (fun q : ℕ ↦ Real.log (size q) / q) atTop (nhds (Real.log 2)) := by
  have hinv : Tendsto (fun q : ℕ ↦ (1 : ℝ) / q) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have heq : (fun q : ℕ ↦ Real.log (size q) / q) =ᶠ[atTop]
      (fun q : ℕ ↦ (1 - 1 / (q : ℝ)) * Real.log 2) := by
    filter_upwards [eventually_ge_atTop 1] with q hq
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    rw [log_size, Nat.cast_sub hq, Nat.cast_one]
    field_simp
  exact Tendsto.congr' heq.symm (by simpa using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).sub hinv).mul_const (Real.log 2))

theorem cutoff_ratio_tendsto : Tendsto (fun q ↦ (cutoff q : ℝ) / size q) atTop (nhds 2) := by
  have heq : (fun q ↦ (cutoff q : ℝ) / size q) =ᶠ[atTop]
      (fun q : ℕ ↦ 2 + (q : ℝ) / size q - 1 / size q) := by
    filter_upwards [eventually_ge_atTop 1] with q hq
    have hN : (size q : ℝ) ≠ 0 := by exact_mod_cast (size_pos q).ne'
    simp only [cutoff, dyadicCutoff, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hq, Nat.cast_one]
    field_simp
    ring
  exact Tendsto.congr' heq.symm (by simpa using (tendsto_const_nhds.add index_div_size_tendsto).sub one_div_size_tendsto)

theorem log_cutoff_over_log_size_tendsto :
    Tendsto (fun q ↦ Real.log (cutoff q) / Real.log (size q)) atTop (nhds 1) := by
  have hlogRatio : Tendsto (fun q ↦ Real.log ((cutoff q : ℝ) / size q)) atTop (nhds (Real.log 2)) :=
    cutoff_ratio_tendsto.log (by norm_num)
  have hrest := hlogRatio.div_atTop log_size_tendsto
  have heq : (fun q ↦ Real.log (cutoff q) / Real.log (size q)) =ᶠ[atTop]
      (fun q ↦ 1 + Real.log ((cutoff q : ℝ) / size q) / Real.log (size q)) := by
    filter_upwards [eventually_ge_atTop 2] with q hq
    have hN : (0 : ℝ) < size q := by exact_mod_cast size_pos q
    have hM : (0 : ℝ) < cutoff q := by
      have h := size_pos q
      exact_mod_cast (show 0 < cutoff q by dsimp [cutoff, dyadicCutoff]; omega)
    have hlogN : Real.log (size q) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < size q by have h := index_le_size (by omega : 1 ≤ q); omega)))
    rw [Real.log_div hM.ne' hN.ne']
    field_simp
    ring
  exact Tendsto.congr' heq.symm (by simpa using tendsto_const_nhds.add hrest)

theorem log_size_over_log_cutoff_tendsto :
    Tendsto (fun q ↦ Real.log (size q) / Real.log (cutoff q)) atTop (nhds 1) := by
  simpa only [inv_div, inv_one] using log_cutoff_over_log_size_tendsto.inv₀ (by norm_num : (1 : ℝ) ≠ 0)

theorem primeCharge_tendsto : Tendsto primeCharge atTop (nhds (2 * Real.log 2)) := by
  have hPNT : Tendsto (fun q ↦ (primeCount (cutoff q) : ℝ) * Real.log (cutoff q) / cutoff q) atTop (nhds 1) := by
    simpa only [PaperP1.LocalRigidityCode.primeCount_eq_primeCounting, Function.comp_def] using
      PaperP1.SharpPrimeCount.prime_counting_ratio_tendsto.comp cutoff_tendsto
  have hproduct := ((hPNT.mul cutoff_ratio_tendsto).mul log_size_over_log_cutoff_tendsto).mul_const (Real.log 2)
  have heq : primeCharge =ᶠ[atTop] (fun q ↦ ((primeCount (cutoff q) : ℝ) * Real.log (cutoff q) / cutoff q) *
      ((cutoff q : ℝ) / size q) * (Real.log (size q) / Real.log (cutoff q)) * Real.log 2) := by
    filter_upwards [eventually_ge_atTop 2] with q _
    have hN : (size q : ℝ) ≠ 0 := by exact_mod_cast (size_pos q).ne'
    have hMNat : 1 < cutoff q := by have h := size_pos q; dsimp [cutoff, dyadicCutoff]; omega
    have hM : (cutoff q : ℝ) ≠ 0 := by exact_mod_cast (by omega : cutoff q ≠ 0)
    have hlogM : Real.log (cutoff q) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hMNat))
    unfold primeCharge
    field_simp
  exact Tendsto.congr' heq.symm (by simpa using hproduct)

end PaperP1.PrimeCylinderScale
