module

public import PaperP1.Analysis.MultiplicativeShortAverage
public import PaperP1.Analysis.SmoothPrefixComparison


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SmoothIntervalProfile
open Finset Nat PaperP1 SmoothPrefixComparison MultiplicativeShortAverage
open scoped Classical

theorem interval_sum (Y j h : ℕ) (hj : 0 < j) :
    (∑ r ∈ range h, OrdinarySmoothIndicator.value Y (j+r)) =
      prefixSum Y (j+h-1)-prefixSum Y (j-1) := by
  have hD : Disjoint (Ioc 0 (j-1)) (Ico j (j+h)) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    have hn' := mem_Ioc.mp hn
    have hm' := mem_Ico.mp hm
    omega
  have hU : Ioc 0 (j-1) ∪ Ico j (j+h) = Ioc 0 (j+h-1) := by
    ext n
    simp only [Finset.mem_union,mem_Ioc,mem_Ico]
    omega
  have he := Finset.sum_union (f := OrdinarySmoothIndicator.value Y) hD
  rw [hU,sum_Ico_eq_sum_range,Nat.add_sub_cancel_left] at he
  unfold prefixSum
  linarith only [he]

theorem short_profile (Y K j h : ℕ) (hY : 1 ≤ Y) (hj : 0 < j) (hh : 0 < h)
    (hEnd : j+h-1 ≤ K) :
    |shortMean (OrdinarySmoothIndicator.value Y) j h-reciprocal Y K| ≤
      2*((roughSet Y K).card : ℝ)/(h : ℝ) := by
  have hStart : j-1 ≤ K := by omega
  have hE := prefix_error Y (j+h-1) K hY hEnd
  have hS := prefix_error Y (j-1) K hY hStart
  have hNat : j+h-1=(j-1)+h := by omega
  have hDiff : ((j+h-1 : ℕ) : ℝ)-((j-1 : ℕ) : ℝ)=(h : ℝ) := by
    rw [hNat,Nat.cast_add]
    ring
  have hRaw : |(prefixSum Y (j+h-1)-prefixSum Y (j-1))-
      (h : ℝ)*reciprocal Y K| ≤ 2*((roughSet Y K).card : ℝ) := by
    calc
      _ = |(prefixSum Y (j+h-1)-((j+h-1 : ℕ) : ℝ)*reciprocal Y K)-
          (prefixSum Y (j-1)-((j-1 : ℕ) : ℝ)*reciprocal Y K)| := by
        congr 1
        rw [← hDiff]
        ring
      _ ≤ |prefixSum Y (j+h-1)-((j+h-1 : ℕ) : ℝ)*reciprocal Y K|+
          |prefixSum Y (j-1)-((j-1 : ℕ) : ℝ)*reciprocal Y K| := abs_sub _ _
      _ ≤ _ := by linarith only [hE,hS]
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  calc
    _ = |(prefixSum Y (j+h-1)-prefixSum Y (j-1))-(h : ℝ)*reciprocal Y K|/(h : ℝ) := by
      rw [shortMean,interval_sum Y j h hj,
        show (prefixSum Y (j+h-1)-prefixSum Y (j-1))/(h : ℝ)-reciprocal Y K =
          ((prefixSum Y (j+h-1)-prefixSum Y (j-1))-(h : ℝ)*reciprocal Y K)/(h : ℝ)
          by field_simp]
      rw [abs_div,abs_of_pos hhR]
    _ ≤ _ := div_le_div_of_nonneg_right hRaw hhR.le

theorem dyadic_profile (Y K N : ℕ) (hY : 1 ≤ Y) (hN : 0 < N) (hEnd : 2*N-1 ≤ K) :
    |longMean (OrdinarySmoothIndicator.value Y) N-reciprocal Y K| ≤
      2*((roughSet Y K).card : ℝ)/(N : ℝ) := by
  have he : longMean (OrdinarySmoothIndicator.value Y) N =
      shortMean (OrdinarySmoothIndicator.value Y) N N := by
    rw [longMean,shortMean,sum_Ico_eq_sum_range,show 2*N-N=N by omega]
  rw [he]
  exact short_profile Y K N N hY hN hN (by omega)

theorem short_long_bound (Y K N j h : ℕ) (hY : 1 ≤ Y) (hN : 0 < N)
    (hj : 0 < j) (hh : 0 < h) (hEnd : j+h-1 ≤ K) (hDyadic : 2*N-1 ≤ K) :
    |shortMean (OrdinarySmoothIndicator.value Y) j h-longMean (OrdinarySmoothIndicator.value Y) N| ≤
      2*((roughSet Y K).card : ℝ)/(h : ℝ)+2*((roughSet Y K).card : ℝ)/(N : ℝ) := by
  calc
    _ ≤ |shortMean (OrdinarySmoothIndicator.value Y) j h-reciprocal Y K|+
        |reciprocal Y K-longMean (OrdinarySmoothIndicator.value Y) N| := abs_sub_le _ _ _
    _ ≤ _ := by
      rw [abs_sub_comm (reciprocal Y K)]
      exact add_le_add (short_profile Y K j h hY hj hh hEnd) (dyadic_profile Y K N hY hN hDyadic)

end PaperP1.SmoothIntervalProfile
