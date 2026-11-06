module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import PaperP1.Analysis.SmoothMobiusConvolution


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SmoothPrefixComparison
open Finset Nat ArithmeticFunction PaperP1 SmoothMobiusConvolution
open scoped Classical

def prefixSum (Y x : ℕ) : ℝ := ∑ n ∈ Ioc 0 x, OrdinarySmoothIndicator.value Y n

def roughSet (Y K : ℕ) : Finset ℕ := (Ioc 0 K).filter fun d ↦ (primorial Y).Coprime d

def reciprocal (Y K : ℕ) : ℝ := ∑ d ∈ Ioc 0 K, roughMobius Y d / (d : ℝ)

theorem prefix_floor (Y x : ℕ) (hY : 1 ≤ Y) :
    prefixSum Y x = ∑ d ∈ Ioc 0 x, roughMobius Y d * ((x/d : ℕ) : ℝ) := by
  have he := sum_Ioc_mul_zeta_eq_sum (roughMobius Y) x
  rw [mul_comm,convolution Y hY] at he
  exact he

theorem prefix_extended (Y x K : ℕ) (hY : 1 ≤ Y) (hxK : x ≤ K) :
    prefixSum Y x = ∑ d ∈ Ioc 0 K, roughMobius Y d * ((x/d : ℕ) : ℝ) := by
  rw [prefix_floor Y x hY]
  apply sum_subset
  · intro d hd
    exact mem_Ioc.mpr ⟨(mem_Ioc.mp hd).1,(mem_Ioc.mp hd).2.trans hxK⟩
  · intro d hd hdx
    have hxd : x < d := by
      have hdP := (mem_Ioc.mp hd).1
      simp only [mem_Ioc] at hdx
      omega
    simp [Nat.div_eq_of_lt hxd]

theorem division_error (x d : ℕ) (hd : 0 < d) :
    |((x/d : ℕ) : ℝ) - (x : ℝ)/(d : ℝ)| ≤ 1 := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hUpper : ((x/d : ℕ) : ℝ) ≤ (x : ℝ)/(d : ℝ) := Nat.cast_div_le
  have hNat : x < (x/d+1)*d := by simpa only [mul_comm] using Nat.lt_mul_div_succ x hd
  have hLower : (x : ℝ)/(d : ℝ) ≤ ((x/d : ℕ) : ℝ)+1 := by
    apply (div_le_iff₀ hdR).mpr
    exact_mod_cast hNat.le
  rw [abs_of_nonpos (sub_nonpos.mpr hUpper)]
  linarith only [hLower]

theorem prefix_error (Y x K : ℕ) (hY : 1 ≤ Y) (hxK : x ≤ K) :
    |prefixSum Y x - (x : ℝ)*reciprocal Y K| ≤ ((roughSet Y K).card : ℝ) := by
  have he : prefixSum Y x - (x : ℝ)*reciprocal Y K =
      ∑ d ∈ Ioc 0 K, roughMobius Y d * (((x/d : ℕ) : ℝ)-(x : ℝ)/(d : ℝ)) := by
    rw [prefix_extended Y x K hY hxK,reciprocal,mul_sum,← sum_sub_distrib]
    apply sum_congr rfl
    intro d hd
    ring
  rw [he]
  calc
    _ ≤ ∑ d ∈ Ioc 0 K, |roughMobius Y d * (((x/d : ℕ) : ℝ)-(x : ℝ)/(d : ℝ))| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Ioc 0 K, if (primorial Y).Coprime d then (1 : ℝ) else 0 := by
      apply sum_le_sum
      intro d hd
      by_cases hc : (primorial Y).Coprime d
      · rw [ite_eq_left hc,abs_mul]
        exact (mul_le_mul_of_nonneg_right (roughMobius_abs Y d) (abs_nonneg _)).trans
          (by simpa only [one_mul] using division_error x d (mem_Ioc.mp hd).1)
      · simp [roughMobius_apply,hc]
    _ = _ := by simp only [roughSet,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem normalized_error (Y x K : ℕ) (hY : 1 ≤ Y) (hx : 0 < x) (hxK : x ≤ K) :
    |prefixSum Y x/(x : ℝ)-reciprocal Y K| ≤ ((roughSet Y K).card : ℝ)/(x : ℝ) := by
  have hxR : 0 < (x : ℝ) := by exact_mod_cast hx
  calc
    _ = |prefixSum Y x-(x : ℝ)*reciprocal Y K|/(x : ℝ) := by
      rw [show prefixSum Y x/(x : ℝ)-reciprocal Y K =
        (prefixSum Y x-(x : ℝ)*reciprocal Y K)/(x : ℝ) by field_simp]
      rw [abs_div,abs_of_pos hxR]
    _ ≤ _ := div_le_div_of_nonneg_right (prefix_error Y x K hY hxK) hxR.le

theorem comparison (Y x z K : ℕ) (hY : 1 ≤ Y) (hx : 0 < x) (hz : 0 < z)
    (hxK : x ≤ K) (hzK : z ≤ K) :
    |prefixSum Y x/(x : ℝ)-prefixSum Y z/(z : ℝ)| ≤
      ((roughSet Y K).card : ℝ)/(x : ℝ)+((roughSet Y K).card : ℝ)/(z : ℝ) := by
  calc
    _ ≤ |prefixSum Y x/(x : ℝ)-reciprocal Y K|+|reciprocal Y K-prefixSum Y z/(z : ℝ)| :=
      abs_sub_le _ _ _
    _ ≤ _ := by
      rw [abs_sub_comm (reciprocal Y K)]
      exact add_le_add (normalized_error Y x K hY hx hxK) (normalized_error Y z K hY hz hzK)

end PaperP1.SmoothPrefixComparison
