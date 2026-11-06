module

public import PaperP1.Arithmetic.PrimeDivisorWeights
public import Mathlib.Data.Nat.Cast.Order.Field

/-! # Exact prime divisibility indicators, floor errors and centered pair moments -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeDivisibilityMoments
open Finset PaperP1
open scoped Classical

def indicator (d n : ℕ) : ℝ := if d ∣ n then 1 else 0

theorem indicator_sum (d X : ℕ) :
    (∑ n ∈ Ioc 0 X, indicator d n) = ((X/d : ℕ) : ℝ) := by
  simpa only [indicator,sum_boole] using congrArg (fun k : ℕ ↦ (k : ℝ))
    (Nat.Ioc_filter_dvd_card_eq_div X d)

theorem indicator_square (d n : ℕ) : (indicator d n)^2 = indicator d n := by
  by_cases h : d ∣ n <;> simp [indicator,h]

theorem indicator_product (p q n : ℕ) (hc : p.Coprime q) :
    indicator p n * indicator q n = indicator (p*q) n := by
  have he : p*q ∣ n ↔ p ∣ n ∧ q ∣ n :=
    ⟨fun h ↦ ⟨dvd_trans (dvd_mul_right p q) h,dvd_trans (dvd_mul_left q p) h⟩,
      fun h ↦ hc.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
  by_cases hp : p ∣ n <;> by_cases hq : q ∣ n <;> simp [indicator,he,hp,hq]

theorem quotient_bounds (X d : ℕ) (hd : 0 < d) :
    (X : ℝ)/(d : ℝ)-1 ≤ ((X/d : ℕ) : ℝ) ∧
      ((X/d : ℕ) : ℝ) ≤ (X : ℝ)/(d : ℝ) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have he : (d : ℝ)*((X/d : ℕ) : ℝ) + ((X%d : ℕ) : ℝ) = X := by
    exact_mod_cast Nat.div_add_mod X d
  have hrem : ((X%d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt X hd
  constructor
  · have hl : (X : ℝ)/(d : ℝ) ≤ ((X/d : ℕ) : ℝ)+1 :=
      (div_le_iff₀ hdr).mpr (by nlinarith)
    linarith
  · exact Nat.cast_div_le

theorem diagonal_bound (X p : ℕ) (hp : 2 ≤ p) :
    (∑ n ∈ Ioc 0 X, (indicator p n-1/(p : ℝ))^2) ≤ (X : ℝ)/(p : ℝ) := by
  have hpr : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hptwo : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hi : (1 : ℝ)/(p : ℝ) ≤ 1/2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hptwo
  have hc := (quotient_bounds X p (by omega)).2
  have he : (∑ n ∈ Ioc 0 X, (indicator p n-1/(p : ℝ))^2) =
      (1-2/(p : ℝ))*((X/p : ℕ) : ℝ) + (X : ℝ)/(p : ℝ)^2 := by
    calc
      _ = ∑ n ∈ Ioc 0 X, ((1-2/(p : ℝ))*indicator p n + 1/(p : ℝ)^2) := by
        apply sum_congr rfl
        intro n hn
        have hs := indicator_square p n
        calc
          _ = (indicator p n)^2 - (2/(p : ℝ))*indicator p n + 1/(p : ℝ)^2 := by ring
          _ = _ := by rw [hs]; ring
      _ = _ := by rw [sum_add_distrib,← mul_sum,indicator_sum]; simp [div_eq_mul_inv]
  rw [he]
  have htwo : 2/(p : ℝ) ≤ 1 := by
    convert mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
  have hm := mul_le_mul_of_nonneg_left hc (by linarith : 0 ≤ 1-2/(p : ℝ))
  have hid : (1-2/(p : ℝ))*((X : ℝ)/(p : ℝ))+(X : ℝ)/(p : ℝ)^2 =
      (X : ℝ)/(p : ℝ)-(X : ℝ)/(p : ℝ)^2 := by ring
  calc
    _ ≤ (1-2/(p : ℝ))*((X : ℝ)/(p : ℝ))+(X : ℝ)/(p : ℝ)^2 := add_le_add hm le_rfl
    _ = _ := hid
    _ ≤ _ := sub_le_self _ (by positivity)

theorem off_diagonal_bound (X p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hc : p.Coprime q) :
    (∑ n ∈ Ioc 0 X, (indicator p n-1/(p : ℝ))*(indicator q n-1/(q : ℝ))) ≤ 1 := by
  have hp0 : 0 < p := by omega
  have hq0 : 0 < q := by omega
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp0
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
  have he : (∑ n ∈ Ioc 0 X, (indicator p n-1/(p : ℝ))*(indicator q n-1/(q : ℝ))) =
      ((X/(p*q) : ℕ) : ℝ) - ((X/p : ℕ) : ℝ)/(q : ℝ) -
        ((X/q : ℕ) : ℝ)/(p : ℝ) + (X : ℝ)/((p : ℝ)*(q : ℝ)) := by
    calc
      _ = ∑ n ∈ Ioc 0 X, (indicator (p*q) n - indicator p n/(q : ℝ) -
          indicator q n/(p : ℝ)+1/((p : ℝ)*(q : ℝ))) := by
        apply sum_congr rfl
        intro n hn
        rw [← indicator_product p q n hc]
        ring
      _ = _ := by rw [sum_add_distrib,sum_sub_distrib,sum_sub_distrib,
        ← sum_div,← sum_div,indicator_sum,indicator_sum,indicator_sum]; simp [div_eq_mul_inv]
  rw [he]
  have hprod : ((X/(p*q) : ℕ) : ℝ) ≤ (X : ℝ)/((p : ℝ)*(q : ℝ)) := by
    simpa only [Nat.cast_mul] using (Nat.cast_div_le (m := X) (n := p*q) (α := ℝ))
  have hlp := div_le_div_of_nonneg_right (quotient_bounds X p hp0).1 hqr.le
  have hlq := div_le_div_of_nonneg_right (quotient_bounds X q hq0).1 hpr.le
  have hip : (1 : ℝ)/(p : ℝ) ≤ 1/2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hp)
  have hiq : (1 : ℝ)/(q : ℝ) ≤ 1/2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hq)
  have hid : ((X : ℝ)/(p : ℝ)-1)/(q : ℝ) + ((X : ℝ)/(q : ℝ)-1)/(p : ℝ) =
      2*((X : ℝ)/((p : ℝ)*(q : ℝ))) - 1/(p : ℝ)-1/(q : ℝ) := by ring
  linarith
end PrimeDivisibilityMoments
