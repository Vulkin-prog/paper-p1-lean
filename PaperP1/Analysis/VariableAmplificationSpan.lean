module

public import PaperP1.Analysis.RoundedAmplificationGeometry

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.VariableAmplificationSpan
open PaperP1

def constant : ℝ := Real.exp 1*(2*Real.sqrt Real.pi+2*Real.pi)

theorem constant_pos : 0 < constant := by unfold constant; positivity

theorem rounded_power_bound (H : ℕ) (hH : 2 ≤ H) (j k : ℕ)
    (hj : (H : ℝ) ≤ NarrowPrimeBands.anchor H j) :
    ((⌈NarrowPrimeBands.growth H*NarrowPrimeBands.anchor H j⌉₊^k : ℕ) : ℝ) ≤
      Real.exp (3*(k : ℝ)/(H : ℝ))*((⌈NarrowPrimeBands.anchor H j⌉₊^k : ℕ) : ℝ) := by
  have hh := pow_le_pow_left₀
    (Nat.cast_nonneg ⌈NarrowPrimeBands.growth H*NarrowPrimeBands.anchor H j⌉₊ :
      (0 : ℝ) ≤ ⌈NarrowPrimeBands.growth H*NarrowPrimeBands.anchor H j⌉₊)
    (RoundedAmplificationGeometry.rounded_upper_exp_bound H hH j hj) k
  rw [mul_pow,← Real.exp_nat_mul] at hh
  have he : (k : ℝ)*(3/(H : ℝ))=3*(k : ℝ)/(H : ℝ) := by ring
  simpa only [he,Nat.cast_pow] using hh

theorem bandwidth_bound (L M : ℕ) (hL : 0 < L) (hLM : L ≤ M) (r : ℝ)
    (hspan : (M : ℝ) ≤ Real.exp (3*r)*(L : ℝ)) :
    0 ≤ Real.log (M : ℝ)-Real.log (L : ℝ) ∧ Real.log (M : ℝ)-Real.log (L : ℝ) ≤ 3*r := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hMp : (0 : ℝ) < M := by exact_mod_cast hL.trans_le hLM
  have hLMe : (L : ℝ) ≤ M := by exact_mod_cast hLM
  have hlo := Real.log_le_log hLp hLMe
  have hup := Real.log_le_log hMp hspan
  rw [Real.log_mul (Real.exp_pos _).ne' hLp.ne',Real.log_exp] at hup
  constructor <;> linarith only [hlo,hup]

theorem sampled_factor_bound (L M T B d r : ℝ) (hL : 1 ≤ L) (hM : 0 ≤ M)
    (hspan : M ≤ Real.exp (3*r)*L) (hT : 0 ≤ T) (hTL : T ≤ L) (hB : 0 ≤ B)
    (hd : 0 ≤ d) (hdr : d ≤ 3*r) (hr : 0 ≤ r) :
    Real.exp 1*(Real.sqrt Real.pi*(T+1)+2*Real.pi*M)*(2+d^2)*(M/L^2*B) ≤
      constant*Real.exp (6*r)*(2+9*r^2)*B := by
  have hLp : 0 < L := by linarith only [hL]
  let s := Real.exp (3*r)
  have hs1 : 1 ≤ s := Real.one_le_exp_iff.mpr (by positivity)
  have hs0 : 0 ≤ s := zero_le_one.trans hs1
  have hs2 : s ≤ s^2 := by nlinarith only [hs1,sq_nonneg (s-1)]
  have ha0 : 0 ≤ M/L := div_nonneg hM hLp.le
  have ha : M/L ≤ s := (div_le_iff₀ hLp).mpr hspan
  have ha2 : (M/L)^2 ≤ s^2 := (sq_le_sq₀ ha0 hs0).mpr ha
  have ht0 : 0 ≤ (T+1)/L := by positivity
  have ht2 : (T+1)/L ≤ 2 := (div_le_iff₀ hLp).mpr (by linarith only [hTL,hL])
  have hfirst : Real.sqrt Real.pi*((T+1)/L)*(M/L) ≤ 2*Real.sqrt Real.pi*s^2 := by
    calc
      _ ≤ (Real.sqrt Real.pi*2)*s := mul_le_mul
        (mul_le_mul_of_nonneg_left ht2 (Real.sqrt_nonneg _)) ha ha0 (by positivity)
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hs2 (by positivity : 0 ≤ 2*Real.sqrt Real.pi)]
  have hsecond := mul_le_mul_of_nonneg_left ha2 (by positivity : 0 ≤ 2*Real.pi)
  have hscalar : Real.sqrt Real.pi*((T+1)/L)*(M/L)+2*Real.pi*(M/L)^2 ≤
      (2*Real.sqrt Real.pi+2*Real.pi)*s^2 := by nlinarith only [hfirst,hsecond]
  have hbase := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscalar (Real.exp_pos 1).le) hB
  have hd2 := pow_le_pow_left₀ hd hdr 2
  have hdf : 2+d^2 ≤ 2+9*r^2 := by nlinarith only [hd2]
  have hbase0 : 0 ≤ Real.exp 1*(Real.sqrt Real.pi*((T+1)/L)*(M/L)+2*Real.pi*(M/L)^2)*B := by positivity
  have he : s^2=Real.exp (6*r) := by
    dsimp only [s]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ = (2+d^2)*(Real.exp 1*(Real.sqrt Real.pi*((T+1)/L)*(M/L)+2*Real.pi*(M/L)^2)*B) := by
      field_simp [hLp.ne']
    _ ≤ (2+9*r^2)*(Real.exp 1*((2*Real.sqrt Real.pi+2*Real.pi)*s^2)*B) :=
      mul_le_mul hdf hbase hbase0 (by positivity)
    _ = _ := by rw [he]; unfold constant; ring
end PaperP1.VariableAmplificationSpan
