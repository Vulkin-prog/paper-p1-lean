module

public import PaperP1.Analysis.PrimeLogDiameter
public import PaperP1.Analysis.DyadicLogBands

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.GeometricBandSplit
open Finset Nat MeasureTheory PaperP1 Filter DyadicLogBands
open scoped Classical

theorem scale_succ (j : ℕ) : scale (j+1)=2*scale j := by
  dsimp only [scale]
  rw [pow_succ]
  ring

theorem scale_sum (J : ℕ) : (∑ j ∈ range J, scale j)=scale J-Real.log 2 := by
  induction J with
  | zero => simp [scale]
  | succ J ih =>
    rw [sum_range_succ,ih,scale_succ]
    ring

theorem scale_sum_le (J : ℕ) : (∑ j ∈ range J, scale j) ≤ scale J := by
  rw [scale_sum]
  exact sub_le_self _ log_two_pos.le

theorem top_scale_upper (X : ℕ) (hX : 2 ≤ X) : scale (count X) ≤ 4*Real.log (X : ℝ) := by
  rw [DyadicLogBands.count,scale_succ]
  have hh := exponent_scale_upper X hX
  linarith

theorem early_sum_bound (X : ℕ) (hX : 2 ≤ X) (m : ℕ) :
    (∑ j ∈ range (count X-m), scale j) ≤ 4*Real.log (X : ℝ)/(2 : ℝ)^m := by
  by_cases hm : m ≤ count X
  · have he : scale (count X-m)*(2 : ℝ)^m=scale (count X) := by
      dsimp only [scale]
      rw [mul_assoc,← pow_add,Nat.sub_add_cancel hm]
    calc
      _ ≤ scale (count X-m) := scale_sum_le _
      _ ≤ _ := (le_div_iff₀ (by positivity : (0 : ℝ) < 2^m)).mpr (by rw [he]; exact top_scale_upper X hX)
  · rw [Nat.sub_eq_zero_of_le (by omega : count X ≤ m),sum_range_zero]
    exact div_nonneg (mul_nonneg (by norm_num) (Real.log_natCast_nonneg X)) (by positivity)

theorem late_count (X m : ℕ) : count X-(count X-m) ≤ m := by omega

theorem range_split {α : Type*} [AddCommMonoid α] (X m : ℕ) (F : ℕ → α) :
    (∑ j ∈ range (count X), F j)=(∑ j ∈ range (count X-m), F j)+
      ∑ j ∈ range (count X-(count X-m)), F ((count X-m)+j) := by
  have he : (count X-m)+(count X-(count X-m))=count X := Nat.add_sub_of_le (Nat.sub_le _ _)
  calc
    _ = ∑ j ∈ range ((count X-m)+(count X-(count X-m))), F j := by rw [he]
    _ = _ := sum_range_add F _ _
end PaperP1.GeometricBandSplit
