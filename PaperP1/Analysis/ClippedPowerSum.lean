module

public import PaperP1.Analysis.PowerSeriesTail

/-! # Clipped reciprocal-power sums and arbitrary finite integer tails -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ClippedPowerSum

open Finset PaperP1.PowerSeriesTail

def clipped (s Y : ℝ) (n : ℕ) : ℝ := min (Y ^ (-s)) ((n + 1 : ℝ) ^ (-s))

theorem clipped_nonneg (s Y : ℝ) (hY : 0 ≤ Y) (n : ℕ) : 0 ≤ clipped s Y n :=
  le_min (Real.rpow_nonneg hY _) (Real.rpow_nonneg (by positivity) _)

theorem clipped_antitone (s Y : ℝ) (hs : 0 ≤ s) : Antitone (clipped s Y) := by
  intro i j hij
  exact min_le_min_left _ (Real.rpow_le_rpow_of_nonpos (by positivity)
    (by exact_mod_cast Nat.add_le_add_right hij 1) (by linarith))

theorem prefix_sum_le (M a : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    (∑ i ∈ range M, if i < a then u else 0) ≤ (a : ℝ) * u := by
  rw [← sum_filter]
  calc
    _ ≤ ∑ _i ∈ range a, u := sum_le_sum_of_subset_of_nonneg
      (fun i hi ↦ mem_range.mpr (mem_filter.mp hi).2) (fun _ _ _ ↦ hu)
    _ = _ := by simp

theorem clipped_sum_le (s Y : ℝ) (hs : 1 < s) (hY : 1 ≤ Y) (M : ℕ) :
    (∑ i ∈ range M, clipped s Y i) ≤ (1 + constant s) * Y ^ (1 - s) := by
  have hYpos : 0 < Y := by linarith
  have hterm (i : ℕ) : clipped s Y i ≤
      (if i < Nat.floor Y then Y ^ (-s) else 0) + tailTerm s Y i := by
    by_cases hi : i < Nat.floor Y
    · rw [ite_eq_left hi]
      exact (min_le_left _ _).trans (le_add_of_nonneg_right (tailTerm_nonneg s Y i))
    · have hgt : Y < (i + 1 : ℝ) := by
        have hf := Nat.lt_floor_add_one Y
        have hcast : (Nat.floor Y : ℝ) ≤ i := by exact_mod_cast (by omega : Nat.floor Y ≤ i)
        linarith
      simp only [ite_eq_right hi, tailTerm, ite_eq_left hgt, zero_add, weight]
      exact min_le_right _ _
  have htail : (∑ i ∈ range M, tailTerm s Y i) ≤ tail s Y :=
    (summable_tailTerm s Y hs).sum_le_tsum (range M) (fun i _ ↦ tailTerm_nonneg s Y i)
  have hfloor : (Nat.floor Y : ℝ) * Y ^ (-s) ≤ Y ^ (1 - s) := by
    calc
      _ ≤ Y * Y ^ (-s) := mul_le_mul_of_nonneg_right (Nat.floor_le hYpos.le) (Real.rpow_nonneg hYpos.le _)
      _ = _ := by
        calc
          _ = Y ^ (1 : ℝ) * Y ^ (-s) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hYpos, sub_eq_add_neg]
  calc
    _ ≤ ∑ i ∈ range M, ((if i < Nat.floor Y then Y ^ (-s) else 0) + tailTerm s Y i) :=
      sum_le_sum (fun i _ ↦ hterm i)
    _ = (∑ i ∈ range M, if i < Nat.floor Y then Y ^ (-s) else 0) +
        ∑ i ∈ range M, tailTerm s Y i := sum_add_distrib
    _ ≤ (Nat.floor Y : ℝ) * Y ^ (-s) + tail s Y :=
      add_le_add (prefix_sum_le M _ _ (Real.rpow_nonneg hYpos.le _)) htail
    _ ≤ Y ^ (1 - s) + constant s * Y ^ (1 - s) :=
      add_le_add hfloor (tail_le_power s hs Y hY)
    _ = _ := by ring

theorem finite_tail_le (S : Finset ℕ) (s Y : ℝ) (hs : 1 < s) (hY : 1 ≤ Y)
    (hS : ∀ n ∈ S, Y < (n : ℝ)) :
    (∑ n ∈ S, (n : ℝ) ^ (-s)) ≤ tail s Y := by
  have hpos (n : ℕ) (hn : n ∈ S) : 1 ≤ n := by
    have h := hS n hn
    have hreal : (1 : ℝ) < n := hY.trans_lt h
    exact_mod_cast hreal.le
  have hinj : Set.InjOn (fun n : ℕ ↦ n - 1) (S : Set ℕ) := by
    intro i hi j hj hij
    have := hpos i hi
    have := hpos j hj
    change i - 1 = j - 1 at hij
    omega
  have heq : (∑ i ∈ S.image (fun n : ℕ ↦ n - 1), tailTerm s Y i) =
      ∑ n ∈ S, (n : ℝ) ^ (-s) := by
    rw [sum_image hinj]
    apply sum_congr rfl
    intro n hn
    have hnat : n - 1 + 1 = n := Nat.sub_add_cancel (hpos n hn)
    have hreal : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast hnat
    simp only [tailTerm, weight, hreal, ite_eq_left (hS n hn)]
  rw [← heq]
  exact (summable_tailTerm s Y hs).sum_le_tsum _ (fun i _ ↦ tailTerm_nonneg s Y i)

theorem finite_tail_le_power (S : Finset ℕ) (s Y : ℝ) (hs : 1 < s) (hY : 1 ≤ Y)
    (hS : ∀ n ∈ S, Y < (n : ℝ)) :
    (∑ n ∈ S, (n : ℝ) ^ (-s)) ≤ constant s * Y ^ (1 - s) :=
  (finite_tail_le S s Y hs hY hS).trans (tail_le_power s hs Y hY)

end PaperP1.ClippedPowerSum
