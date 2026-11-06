module

public import PaperP1.Analysis.FloorAmplificationOrder

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.CeilingAmplificationOrder
open PaperP1

def order (N : ℕ) (u : ℝ) : ℕ := ⌈Real.log (N : ℝ)/Real.log u⌉₊

theorem logarithmic_lower (N : ℕ) (u : ℝ) (hu : 1 < u) :
    Real.log (N : ℝ) ≤ (order N u : ℝ)*Real.log u := by
  have hlog := Real.log_pos hu
  exact (div_le_iff₀ hlog).mp (Nat.le_ceil _)

theorem logarithmic_upper (N : ℕ) (u : ℝ) (hu : 1 < u) :
    (order N u : ℝ)*Real.log u ≤ Real.log (N : ℝ)+Real.log u := by
  have hlog := Real.log_pos hu
  have hh := (Nat.ceil_lt_add_one (div_nonneg (Real.log_natCast_nonneg N) hlog.le)).le
  change (order N u : ℝ) ≤ Real.log (N : ℝ)/Real.log u+1 at hh
  have hm := mul_le_mul_of_nonneg_right hh hlog.le
  have he : (Real.log (N : ℝ)/Real.log u+1)*Real.log u=Real.log (N : ℝ)+Real.log u := by
    field_simp
  exact hm.trans_eq he

theorem power_lower (N : ℕ) (hN : 0 < N) (u : ℝ) (hu : 1 < u) :
    (N : ℝ) ≤ u^(order N u) := by
  have hup : 0 < u := by linarith only [hu]
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hh := Real.exp_le_exp.mpr (logarithmic_lower N u hu)
  rw [Real.exp_log hNp,Real.exp_nat_mul,Real.exp_log hup] at hh
  exact hh

theorem power_upper (N : ℕ) (hN : 1 ≤ N) (u : ℝ) (hu : 1 < u) :
    u^(order N u) ≤ u*(N : ℝ) := by
  have hup : 0 < u := by linarith only [hu]
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hh := Real.exp_le_exp.mpr (logarithmic_upper N u hu)
  rw [Real.exp_nat_mul,Real.exp_log hup,Real.exp_add,Real.exp_log hNp,Real.exp_log hup] at hh
  simpa only [mul_comm] using hh

theorem order_le (N H : ℕ) (u : ℝ) (hu : 1 < u)
    (hlog : Real.log (N : ℝ) ≤ (H : ℝ)*Real.log u) : order N u ≤ H := by
  exact Nat.ceil_le.mpr ((div_le_iff₀ (Real.log_pos hu)).mpr hlog)

theorem rounded_power_lower (N : ℕ) (hN : 0 < N) (u : ℝ) (hu : 1 < u) :
    (N : ℝ) ≤ ((⌈u⌉₊^(order N u) : ℕ) : ℝ) := by
  have hp := pow_le_pow_left₀ (by linarith only [hu] : 0 ≤ u) (Nat.le_ceil u) (order N u)
  rw [← Nat.cast_pow] at hp
  exact (power_lower N hN u hu).trans hp
end PaperP1.CeilingAmplificationOrder
