module

public import PaperP1.Analysis.LogarithmicScaleCover
public import PaperP1.Arithmetic.OddPrimePivot
public import PaperP1.Combinatorics.GraphStarWeights

/-! # Exact finite reciprocal mass from a fixed logarithmic pivot cover

Each band retains its own reciprocal weight. The finite counting premises
are explicit; the asymptotic application supplies them internally.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteLogarithmicPivotMass

open Finset OddPrimePivot

theorem band_cost (K : ℕ) (hK : 1 ≤ K) (j : Fin (3 * K)) (η : ℝ) :
    2 - 1 / (K : ℝ) - η ≤ (j.val : ℝ) / K +
      (1 / (((j.val + 1 : ℕ) : ℝ) / K) - η) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  let x := ((j.val + 1 : ℕ) : ℝ) / K
  have hx : 0 < x := by dsimp only [x]; positivity
  have hxinv : 2 ≤ x + 1 / x := by
    rw [show x + 1 / x = (x ^ 2 + 1) / x by field_simp]
    exact (le_div_iff₀ hx).mpr (by nlinarith only [sq_nonneg (x - 1)])
  have hrel : (j.val : ℝ) / K + 1 / (K : ℝ) = x := by dsimp only [x]; push_cast; ring
  change 2 - 1 / (K : ℝ) - η ≤ (j.val : ℝ) / K + (1 / x - η)
  linarith only [hxinv, hrel]

theorem finite_mass (N K : ℕ) (hK : 1 ≤ K) (V η : ℝ) (hV : 0 < V) (hη : 0 ≤ η)
    (S : Finset ℕ) (hS : S ⊆ Icc 1 (3 * N))
    (hcount : ∀ j : Fin (3 * K),
      ((S.filter (fun n ↦ (largestOddPrime n : ℝ) ≤ Real.exp (((j.val + 1 : ℕ) : ℝ) / K * V))).card : ℝ) ≤
        (N : ℝ) * Real.exp (-(1 / (((j.val + 1 : ℕ) : ℝ) / K) - η) * V)) :
    (∑ n ∈ S, 1 / (largestOddPrime n : ℝ)) ≤
      (3 * (K : ℝ) + 3) * N * Real.exp (-(2 - 1 / (K : ℝ) - η) * V) := by
  classical
  let a (j : Fin (3 * K)) : ℝ := (j.val : ℝ) / K
  let A (j : Fin (3 * K)) : ℝ := ((j.val + 1 : ℕ) : ℝ) / K
  let b (j : Fin (3 * K)) : ℝ := 1 / A j - η
  let c := 2 - 1 / (K : ℝ) - η
  let U (j : Fin (3 * K)) := S.filter fun n ↦
    Real.exp (a j * V) ≤ (largestOddPrime n : ℝ) ∧ (largestOddPrime n : ℝ) ≤ Real.exp (A j * V)
  let T := S.filter fun n ↦ Real.exp (3 * V) < (largestOddPrime n : ℝ)
  let w (n : ℕ) : ℝ := 1 / (largestOddPrime n : ℝ)
  have hw (n : ℕ) : 0 ≤ w n := by dsimp only [w]; positivity
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hc : c ≤ 3 := by
    dsimp only [c]
    have hi : 0 ≤ 1 / (K : ℝ) := by positivity
    linarith only [hi, hη]
  have hcoef (j : Fin (3 * K)) : c ≤ a j + b j := band_cost K hK j η
  have hcover : S ⊆ T ∪ univ.biUnion U := by
    intro n hn
    by_cases hp : (largestOddPrime n : ℝ) ≤ Real.exp (3 * V)
    · have hunit : (1 : ℝ) ≤ largestOddPrime n := by exact_mod_cast largestOddPrime_pos n
      obtain ⟨j, hj, hl, hu⟩ := LogarithmicScaleCover.exponential_cover K hK V (largestOddPrime n : ℝ) hV hunit hp
      exact mem_union_right _ (mem_biUnion.mpr
        ⟨⟨j, mem_range.mp hj⟩, mem_univ _, mem_filter.mpr ⟨hn, hl, hu⟩⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨hn, lt_of_not_ge hp⟩)
  have hUcard (j : Fin (3 * K)) : ((U j).card : ℝ) ≤ (N : ℝ) * Real.exp (-b j * V) := by
    have hsub : U j ⊆ S.filter (fun n ↦ (largestOddPrime n : ℝ) ≤ Real.exp (A j * V)) := by
      intro n hn
      obtain ⟨hnS, _hl, hu⟩ := mem_filter.mp hn
      exact mem_filter.mpr ⟨hnS, hu⟩
    have hh : ((U j).card : ℝ) ≤ ((S.filter (fun n ↦ (largestOddPrime n : ℝ) ≤ Real.exp (A j * V))).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    exact hh.trans (hcount j)
  have hUmass (j : Fin (3 * K)) : (∑ n ∈ U j, w n) ≤ (N : ℝ) * Real.exp (-c * V) := by
    have hweight (n : ℕ) (hn : n ∈ U j) : w n ≤ Real.exp (-(a j * V)) := by
      have hl := (mem_filter.mp hn).2.1
      calc
        _ ≤ 1 / Real.exp (a j * V) := one_div_le_one_div_of_le (Real.exp_pos _) hl
        _ = _ := by rw [Real.exp_neg, one_div]
    calc
      _ ≤ ∑ _n ∈ U j, Real.exp (-(a j * V)) := sum_le_sum hweight
      _ = ((U j).card : ℝ) * Real.exp (-(a j * V)) := by simp
      _ ≤ ((N : ℝ) * Real.exp (-b j * V)) * Real.exp (-(a j * V)) :=
        mul_le_mul_of_nonneg_right (hUcard j) (Real.exp_nonneg _)
      _ = (N : ℝ) * Real.exp (-(a j + b j) * V) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right (hcoef j) hV.le
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith only [hh])) (Nat.cast_nonneg N)
  have hTcard : (T.card : ℝ) ≤ 3 * N := by
    have hh : T.card ≤ 3 * N := (card_le_card ((filter_subset _ _).trans hS)).trans_eq (by simp)
    exact_mod_cast hh
  have hTmass : (∑ n ∈ T, w n) ≤ 3 * N * Real.exp (-c * V) := by
    have hweight (n : ℕ) (hn : n ∈ T) : w n ≤ Real.exp (-(3 * V)) := by
      have hl := (mem_filter.mp hn).2
      calc
        _ ≤ 1 / Real.exp (3 * V) := one_div_le_one_div_of_le (Real.exp_pos _) hl.le
        _ = _ := by rw [Real.exp_neg, one_div]
    calc
      _ ≤ ∑ _n ∈ T, Real.exp (-(3 * V)) := sum_le_sum hweight
      _ = (T.card : ℝ) * Real.exp (-(3 * V)) := by simp
      _ ≤ (3 * N : ℝ) * Real.exp (-(3 * V)) := mul_le_mul_of_nonneg_right hTcard (Real.exp_nonneg _)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hc hV.le
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith only [hh])) (by positivity)
  have hBands : (∑ j : Fin (3 * K), ∑ n ∈ U j, w n) ≤
      ((3 * K : ℕ) : ℝ) * ((N : ℝ) * Real.exp (-c * V)) := by
    calc
      _ ≤ ∑ _j : Fin (3 * K), (N : ℝ) * Real.exp (-c * V) := sum_le_sum (fun j _ ↦ hUmass j)
      _ = _ := by simp
  have h0 := sum_le_sum_of_subset_of_nonneg hcover (fun n _ _ ↦ hw n)
  have h1 := GraphStarWeights.sum_union_le_nonneg T (univ.biUnion U) w hw
  have h2 := GraphStarWeights.sum_biUnion_le_nonneg univ U w hw
  change (∑ n ∈ S, w n) ≤ (3 * (K : ℝ) + 3) * N * Real.exp (-c * V)
  push_cast at hBands
  nlinarith only [h0, h1, h2, hTmass, hBands]

end PaperP1.FiniteLogarithmicPivotMass
