module

public import PaperP1.Analysis.NarrowRamareRectangle

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.RoundedAmplificationGeometry
open Finset PaperP1
open scoped Classical

theorem rounded_upper_bound (H j : ℕ) :
    (⌈NarrowPrimeBands.growth H*NarrowPrimeBands.anchor H j⌉₊ : ℝ) ≤
      (NarrowPrimeBands.growth H+1/NarrowPrimeBands.anchor H j)*(⌈NarrowPrimeBands.anchor H j⌉₊ : ℝ) := by
  have hu := NarrowPrimeBands.anchor_pos H j
  have hc : 0 ≤ NarrowPrimeBands.growth H := zero_le_one.trans (NarrowPrimeBands.growth_one_le H)
  calc
    _ ≤ NarrowPrimeBands.growth H*NarrowPrimeBands.anchor H j+1 :=
      (Nat.ceil_lt_add_one (mul_nonneg hc hu.le)).le
    _ = (NarrowPrimeBands.growth H+1/NarrowPrimeBands.anchor H j)*NarrowPrimeBands.anchor H j := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.le_ceil _) (add_nonneg hc (by positivity))

theorem rounded_upper_exp_bound (H : ℕ) (hH : 2 ≤ H) (j : ℕ) (hj : (H : ℝ) ≤ NarrowPrimeBands.anchor H j) :
    (⌈NarrowPrimeBands.growth H*NarrowPrimeBands.anchor H j⌉₊ : ℝ) ≤
      Real.exp (3/(H : ℝ))*(⌈NarrowPrimeBands.anchor H j⌉₊ : ℝ) := by
  have hHp : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hr := one_div_le_one_div_of_le hHp hj
  have he := NarrowPrimeBands.growth_error H hH
  have hs : NarrowPrimeBands.growth H+1/NarrowPrimeBands.anchor H j ≤ Real.exp (3/(H : ℝ)) := by
    calc
      _ ≤ (1+2/(H : ℝ))+1/(H : ℝ) := add_le_add (by linarith only [he]) hr
      _ = 1+3/(H : ℝ) := by ring
      _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (3/(H : ℝ))
  exact (rounded_upper_bound H j).trans (mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg _))

theorem rounded_power_bound (H : ℕ) (hH : 2 ≤ H) (j k : ℕ) (hj : (H : ℝ) ≤ NarrowPrimeBands.anchor H j)
    (hk : k ≤ H) :
    ((⌈NarrowPrimeBands.growth H*NarrowPrimeBands.anchor H j⌉₊^k : ℕ) : ℝ) ≤
      Real.exp 3*((⌈NarrowPrimeBands.anchor H j⌉₊^k : ℕ) : ℝ) := by
  have hHp : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hkR : (k : ℝ) ≤ H := by exact_mod_cast hk
  have harg : (k : ℝ)*(3/(H : ℝ)) ≤ 3 := by
    calc
      _ ≤ (H : ℝ)*(3/(H : ℝ)) := mul_le_mul_of_nonneg_right hkR (by positivity)
      _ = _ := by field_simp
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg ⌈NarrowPrimeBands.growth H*NarrowPrimeBands.anchor H j⌉₊ :
    (0 : ℝ) ≤ ⌈NarrowPrimeBands.growth H*NarrowPrimeBands.anchor H j⌉₊) (rounded_upper_exp_bound H hH j hj) k
  rw [mul_pow,← Real.exp_nat_mul] at hp
  simp only [Nat.cast_pow]
  exact hp.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr harg) (by positivity))

theorem product_span_bound (X H j l k : ℕ) (hX : 0 < X) (hH : 2 ≤ H)
    (hj : (H : ℝ) ≤ NarrowPrimeBands.anchor H j) (hk : k ≤ H) :
    ((⌈NarrowPrimeBands.growth H*NarrowPrimeBands.anchor H j⌉₊^k*
      ⌈2*(X : ℝ)/NarrowPrimeBands.anchor H l⌉₊ : ℕ) : ℝ) ≤
    2*Real.exp 3*((⌈NarrowPrimeBands.anchor H j⌉₊^k*
      ⌈(X : ℝ)/NarrowPrimeBands.anchor H l⌉₊ : ℕ) : ℝ) := by
  have hp := rounded_power_bound H hH j k hj hk
  have hm : (⌈2*(X : ℝ)/NarrowPrimeBands.anchor H l⌉₊ : ℝ) ≤
      2*(⌈(X : ℝ)/NarrowPrimeBands.anchor H l⌉₊ : ℝ) := by
    exact_mod_cast (NarrowRamareRectangle.cofactor_endpoints X H l hX).2.2
  have hh := mul_le_mul hp hm (Nat.cast_nonneg _) (by positivity : (0 : ℝ) ≤
    Real.exp 3*((⌈NarrowPrimeBands.anchor H j⌉₊^k : ℕ) : ℝ))
  push_cast at hh ⊢
  nlinarith only [hh]

theorem bandwidth_bound (L M : ℕ) (hL : 0 < L) (hLM : L ≤ M)
    (hspan : (M : ℝ) ≤ 2*Real.exp 3*(L : ℝ)) :
    0 ≤ Real.log (M : ℝ)-Real.log (L : ℝ) ∧ Real.log (M : ℝ)-Real.log (L : ℝ) ≤ 4 := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hMp : (0 : ℝ) < M := by exact_mod_cast hL.trans_le hLM
  have hLMe : (L : ℝ) ≤ M := by exact_mod_cast hLM
  have hlo := Real.log_le_log hLp hLMe
  have hup := Real.log_le_log hMp hspan
  rw [Real.log_mul (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_pos 3).ne') hLp.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_pos 3).ne',Real.log_exp] at hup
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  constructor <;> linarith only [hlo,hup,htwo]
end PaperP1.RoundedAmplificationGeometry
