module

public import PaperP1.Analysis.FiniteLogarithmicPivotMass

/-! # Finite weighted pivot covers with an arbitrary number of bands

The count and cost hypotheses are explicit finite premises. The endpoints,
including one and the last upper cutoff, are retained without disjointness.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MovingLogarithmicPivotMass

open Finset OddPrimePivot

theorem interval_cover (K : ℕ) (hK : 1 ≤ K) (t : ℝ) (ht : 0 ≤ t) (htK : t ≤ K) :
    ∃ j ∈ range K, (j : ℝ) ≤ t ∧ t ≤ ((j + 1 : ℕ) : ℝ) := by
  have hfloor := Nat.floor_le ht
  by_cases hj : ⌊t⌋₊ < K
  · refine ⟨⌊t⌋₊, mem_range.mpr hj, hfloor, ?_⟩
    exact_mod_cast (Nat.lt_floor_add_one t).le
  · have hKfloor : (K : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast (show K ≤ ⌊t⌋₊ by omega)
    have heq : t = K := le_antisymm htK (hKfloor.trans hfloor)
    refine ⟨K - 1, mem_range.mpr (by omega), ?_, ?_⟩
    · rw [heq]
      exact_mod_cast Nat.sub_le K 1
    · rw [heq, show K - 1 + 1 = K by omega]

theorem exponential_cover (K : ℕ) (hK : 1 ≤ K) (w p : ℝ) (hw : 0 < w)
    (hp : 1 ≤ p) (hupper : p ≤ Real.exp ((K : ℝ) * w)) :
    ∃ j ∈ range K, Real.exp ((j : ℝ) * w) ≤ p ∧
      p ≤ Real.exp (((j + 1 : ℕ) : ℝ) * w) := by
  have hp0 : 0 < p := by linarith only [hp]
  have hh := Real.log_le_log hp0 hupper
  rw [Real.log_exp] at hh
  obtain ⟨j, hj, hl, hu⟩ := interval_cover K hK (Real.log p / w)
    (div_nonneg (Real.log_nonneg hp) hw.le) ((div_le_iff₀ hw).mpr hh)
  refine ⟨j, hj, ?_, ?_⟩
  · calc
      _ ≤ Real.exp (Real.log p) := Real.exp_le_exp.mpr ((le_div_iff₀ hw).mp hl)
      _ = _ := Real.exp_log hp0
  · calc
      _ = Real.exp (Real.log p) := (Real.exp_log hp0).symm
      _ ≤ _ := Real.exp_le_exp.mpr ((div_le_iff₀ hw).mp hu)

theorem finite_mass (N K : ℕ) (hK : 1 ≤ K) (w H u E V err : ℝ)
    (hw : 0 < w) (hV : 0 < V) (herr : 0 ≤ err) (htail : 3 * V ≤ (K : ℝ) * w)
    (S : Finset ℕ) (hS : S ⊆ Icc 1 (3 * N))
    (hcost : ∀ v : ℝ, 0 < v → 2 * V - err ≤ v + H * u / v - E)
    (hcount : ∀ j : Fin K,
      ((S.filter (fun n ↦ (largestOddPrime n : ℝ) ≤ Real.exp (((j.val + 1 : ℕ) : ℝ) * w))).card : ℝ) ≤
        3 * N * Real.exp (-H * u / (((j.val + 1 : ℕ) : ℝ) * w) + E + err)) :
    (∑ n ∈ S, 1 / (largestOddPrime n : ℝ)) ≤
      (3 * (K : ℝ) + 3) * N * Real.exp (-2 * V + w + 2 * err) := by
  classical
  let B := -2 * V + w + 2 * err
  let U (j : Fin K) := S.filter fun n ↦
    Real.exp ((j.val : ℝ) * w) ≤ (largestOddPrime n : ℝ) ∧
      (largestOddPrime n : ℝ) ≤ Real.exp (((j.val + 1 : ℕ) : ℝ) * w)
  let T := S.filter fun n ↦ Real.exp ((K : ℝ) * w) < (largestOddPrime n : ℝ)
  let f (n : ℕ) : ℝ := 1 / (largestOddPrime n : ℝ)
  have hf (n : ℕ) : 0 ≤ f n := by dsimp only [f]; positivity
  have hcover : S ⊆ T ∪ univ.biUnion U := by
    intro n hn
    by_cases hp : (largestOddPrime n : ℝ) ≤ Real.exp ((K : ℝ) * w)
    · have hunit : (1 : ℝ) ≤ largestOddPrime n := by exact_mod_cast largestOddPrime_pos n
      obtain ⟨j, hj, hl, hu⟩ := exponential_cover K hK w (largestOddPrime n : ℝ) hw hunit hp
      exact mem_union_right _ (mem_biUnion.mpr
        ⟨⟨j, mem_range.mp hj⟩, mem_univ _, mem_filter.mpr ⟨hn, hl, hu⟩⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨hn, lt_of_not_ge hp⟩)
  have hUcard (j : Fin K) : ((U j).card : ℝ) ≤
      3 * N * Real.exp (-H * u / (((j.val + 1 : ℕ) : ℝ) * w) + E + err) := by
    have hs : U j ⊆ S.filter (fun n ↦ (largestOddPrime n : ℝ) ≤ Real.exp (((j.val + 1 : ℕ) : ℝ) * w)) := by
      intro n hn
      obtain ⟨hnS, _hl, hu⟩ := mem_filter.mp hn
      exact mem_filter.mpr ⟨hnS, hu⟩
    have hc : ((U j).card : ℝ) ≤ ((S.filter (fun n ↦ (largestOddPrime n : ℝ) ≤ Real.exp (((j.val + 1 : ℕ) : ℝ) * w))).card : ℝ) := by
      exact_mod_cast card_le_card hs
    exact hc.trans (hcount j)
  have hUmass (j : Fin K) : (∑ n ∈ U j, f n) ≤ 3 * N * Real.exp B := by
    have hweight (n : ℕ) (hn : n ∈ U j) : f n ≤ Real.exp (-(j.val : ℝ) * w) := by
      have hl := (mem_filter.mp hn).2.1
      calc
        _ ≤ 1 / Real.exp ((j.val : ℝ) * w) := one_div_le_one_div_of_le (Real.exp_pos _) hl
        _ = _ := by rw [show -(j.val : ℝ) * w = -((j.val : ℝ) * w) by ring, Real.exp_neg, one_div]
    have hc := hcost (((j.val + 1 : ℕ) : ℝ) * w) (by positivity)
    have hb : -H * u / (((j.val + 1 : ℕ) : ℝ) * w) + E + err + -(j.val : ℝ) * w ≤ B := by
      dsimp only [B]
      push_cast at hc ⊢
      simp only [neg_mul, neg_div]
      nlinarith only [hc]
    calc
      _ ≤ ∑ _n ∈ U j, Real.exp (-(j.val : ℝ) * w) := sum_le_sum hweight
      _ = ((U j).card : ℝ) * Real.exp (-(j.val : ℝ) * w) := by simp
      _ ≤ (3 * N * Real.exp (-H * u / (((j.val + 1 : ℕ) : ℝ) * w) + E + err)) *
          Real.exp (-(j.val : ℝ) * w) := mul_le_mul_of_nonneg_right (hUcard j) (Real.exp_nonneg _)
      _ = 3 * N * Real.exp (-H * u / (((j.val + 1 : ℕ) : ℝ) * w) + E + err + -(j.val : ℝ) * w) := by
        rw [mul_assoc, ← Real.exp_add]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hb) (by positivity)
  have hTcard : (T.card : ℝ) ≤ 3 * N := by
    have hh : T.card ≤ 3 * N := (card_le_card ((filter_subset _ _).trans hS)).trans_eq (by simp)
    exact_mod_cast hh
  have hTmass : (∑ n ∈ T, f n) ≤ 3 * N * Real.exp B := by
    have hweight (n : ℕ) (hn : n ∈ T) : f n ≤ Real.exp (-((K : ℝ) * w)) := by
      have hl := (mem_filter.mp hn).2
      calc
        _ ≤ 1 / Real.exp ((K : ℝ) * w) := one_div_le_one_div_of_le (Real.exp_pos _) hl.le
        _ = _ := by rw [Real.exp_neg, one_div]
    calc
      _ ≤ ∑ _n ∈ T, Real.exp (-((K : ℝ) * w)) := sum_le_sum hweight
      _ = (T.card : ℝ) * Real.exp (-((K : ℝ) * w)) := by simp
      _ ≤ (3 * N : ℝ) * Real.exp (-((K : ℝ) * w)) := mul_le_mul_of_nonneg_right hTcard (Real.exp_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by dsimp only [B]; linarith only [htail, hw, hV, herr])) (by positivity)
  have hBands : (∑ j : Fin K, ∑ n ∈ U j, f n) ≤ (K : ℝ) * (3 * N * Real.exp B) := by
    calc
      _ ≤ ∑ _j : Fin K, 3 * N * Real.exp B := sum_le_sum (fun j _ ↦ hUmass j)
      _ = _ := by simp
  have h0 := sum_le_sum_of_subset_of_nonneg hcover (fun n _ _ ↦ hf n)
  have h1 := GraphStarWeights.sum_union_le_nonneg T (univ.biUnion U) f hf
  have h2 := GraphStarWeights.sum_biUnion_le_nonneg univ U f hf
  change (∑ n ∈ S, f n) ≤ (3 * (K : ℝ) + 3) * N * Real.exp B
  nlinarith only [h0, h1, h2, hTmass, hBands]

end PaperP1.MovingLogarithmicPivotMass
