module

public import PaperP1.Analysis.NarrowRamareRectangle

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FloorAmplificationOrder
open PaperP1
open scoped Classical

def order (u q : ℝ) : ℕ := ⌊Real.log q/Real.log u⌋₊

theorem logarithmic_upper (u q : ℝ) (hu : 1 < u) (hq : 1 ≤ q) :
    (order u q : ℝ)*Real.log u ≤ Real.log q := by
  have hlog := Real.log_pos hu
  have hqlog := Real.log_nonneg hq
  have hh := Nat.floor_le (div_nonneg hqlog hlog.le)
  exact (le_div_iff₀ hlog).mp hh

theorem power_lower (u q : ℝ) (hu : 1 < u) (hq : 0 < q) :
    q/u ≤ u^(order u q) := by
  have hup : 0 < u := by linarith
  have hlog := Real.log_pos hu
  have hh := Nat.lt_floor_add_one (Real.log q/Real.log u)
  have hl : Real.log q < ((order u q : ℝ)+1)*Real.log u := (div_lt_iff₀ hlog).mp hh
  have he : Real.exp (((order u q : ℝ)+1)*Real.log u)=u^(order u q)*u := by
    rw [add_mul,Real.exp_add,one_mul,Real.exp_nat_mul,Real.exp_log hup]
  have hpow := Real.exp_lt_exp.mpr hl
  rw [Real.exp_log hq,he] at hpow
  exact ((div_lt_iff₀ hup).mpr hpow).le

theorem order_le_floor_cube (x u q : ℝ) (hu : 1 < u) (hq : 1 ≤ q)
    (hlogu : 1 ≤ Real.log u) (hlogq : Real.log q ≤ x^3) : order u q ≤ ⌊x^3⌋₊ := by
  apply Nat.floor_le_floor
  have hlog := Real.log_pos hu
  have hqlog := Real.log_nonneg hq
  exact ((div_le_iff₀ hlog).mpr (by nlinarith only [hlogu,hqlog])).trans hlogq

theorem rounded_product_lower (X u q : ℝ) (hX : 0 ≤ X) (hu : 1 < u) (hq : 1 ≤ q) :
    X/u ≤ ((⌈u⌉₊^(order u q)*⌈X/q⌉₊ : ℕ) : ℝ) := by
  have hup : 0 < u := by linarith
  have hqp : 0 < q := by linarith
  have hpow : u^(order u q) ≤ (⌈u⌉₊ : ℝ)^(order u q) :=
    pow_le_pow_left₀ hup.le (Nat.le_ceil u) (order u q)
  calc
    X/u = (q/u)*(X/q) := by field_simp
    _ ≤ (⌈u⌉₊ : ℝ)^(order u q)*(⌈X/q⌉₊ : ℝ) :=
      mul_le_mul ((power_lower u q hu hqp).trans hpow) (Nat.le_ceil _)
        (div_nonneg hX hqp.le) (by positivity)
    _ = _ := by push_cast; rfl

theorem short_height_bound (X : ℕ) (u q T : ℝ) (hu : 1 < u) (hq : 1 ≤ q)
    (hcap : u ≤ Real.log (X : ℝ)) (hT : T ≤ (X : ℝ)/Real.log (X : ℝ)) :
    T ≤ ((⌈u⌉₊^(order u q)*⌈(X : ℝ)/q⌉₊ : ℕ) : ℝ) := by
  have hup : 0 < u := by linarith
  exact hT.trans ((div_le_div_of_nonneg_left (Nat.cast_nonneg X : (0 : ℝ) ≤ X) hup hcap).trans
    (rounded_product_lower X u q (Nat.cast_nonneg X) hu hq))
end PaperP1.FloorAmplificationOrder
