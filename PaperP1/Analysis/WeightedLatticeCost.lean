module

public import PaperP1.Analysis.WeightedLatticeTriangle
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Pairwise
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Sharp total logarithmic cost of any distinct lattice monomials -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedLatticeCost

open Finset PaperP1.WeightedLatticeTriangle

theorem sqrt_increment (n : ℕ) :
    (2 / 3 : ℝ) * (((n : ℝ) + 1) * Real.sqrt (n + 1) - n * Real.sqrt n) ≤
      Real.sqrt (n + 1) := by
  by_cases hn : n = 0
  · subst n
    norm_num
  · have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hleft : 0 ≤ (2 * (n : ℝ) - 1) * Real.sqrt (n + 1) :=
      mul_nonneg (by linarith only [hn₁]) (Real.sqrt_nonneg _)
    have hright : 0 ≤ 2 * (n : ℝ) * Real.sqrt n := by positivity
    have hs : ((2 * (n : ℝ) - 1) * Real.sqrt (n + 1)) ^ 2 ≤
        (2 * (n : ℝ) * Real.sqrt n) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (Nat.cast_nonneg n)]
      nlinarith only [hn₁]
    have hroot := (sq_le_sq₀ hleft hright).mp hs
    linarith only [hroot]

theorem sum_sqrt_lower (n : ℕ) :
    (2 / 3 : ℝ) * n * Real.sqrt n ≤ ∑ j ∈ range n, Real.sqrt ((j : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hstep := sqrt_increment n
    simp only [Nat.cast_add, Nat.cast_one]
    linarith only [ih, hstep]

theorem sorted_enumeration (S : Finset (ℕ × ℕ)) (r₁ r₂ : ℝ) :
    ∃ e : Fin S.card → ℕ × ℕ, Function.Injective e ∧ univ.image e = S ∧
      Monotone (fun i ↦ cost r₁ r₂ (e i)) := by
  classical
  let r : (ℕ × ℕ) → (ℕ × ℕ) → Prop := fun p q ↦ cost r₁ r₂ p ≤ cost r₁ r₂ q
  let : IsTrans (ℕ × ℕ) r := ⟨fun _ _ _ ↦ le_trans⟩
  let : Std.Total r := ⟨fun _ _ ↦ le_total _ _⟩
  let l := S.toList.mergeSort (fun p q ↦ decide (r p q))
  have hperm : l.Perm S.toList := List.mergeSort_perm _ _
  have hlen : l.length = S.card := hperm.length_eq.trans (length_toList S)
  have hnodup : l.Nodup := hperm.nodup_iff.mpr (nodup_toList S)
  have hsort : l.Pairwise r := List.pairwise_mergeSort' r S.toList
  let e : Fin S.card → ℕ × ℕ := fun i ↦ l.get ⟨i.val, by rw [hlen]; exact i.isLt⟩
  have he : Function.Injective e := by
    intro i j hij
    have hfin := (List.nodup_iff_injective_get.mp hnodup) hij
    exact Fin.ext (congrArg (fun j : Fin l.length ↦ j.val) hfin)
  have hmem (i : Fin S.card) : e i ∈ S := by
    apply mem_toList.mp
    exact hperm.mem_iff.mp (List.get_mem _ _)
  have hsubset : univ.image e ⊆ S := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := mem_image.mp hp
    exact hmem i
  refine ⟨e, he, eq_of_subset_of_card_le hsubset ?_, ?_⟩
  · rw [card_image_of_injective _ he, card_univ, Fintype.card_fin]
  · intro i j hij
    exact hsort.rel_get_of_le hij

theorem sorted_point_lower (n : ℕ) (e : Fin n → ℕ × ℕ) (he : Function.Injective e)
    (r₁ r₂ : ℝ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hmono : Monotone (fun i ↦ cost r₁ r₂ (e i))) (i : Fin n) :
    Real.sqrt (2 * r₁ * r₂) * Real.sqrt ((i.val : ℝ) + 1) - (r₁ + r₂) ≤
      cost r₁ r₂ (e i) := by
  have hcost : 0 ≤ cost r₁ r₂ (e i) := by unfold cost; positivity
  have hcard := triangle_card_bound ((Iic i).image e) r₁ r₂ (cost r₁ r₂ (e i))
    hr₁ hr₂ hcost (by
      intro p hp
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hp
      exact hmono (mem_Iic.mp hj))
  rw [card_image_of_injective _ he, Fin.card_Iic] at hcard
  have hsq : 2 * r₁ * r₂ * ((i.val : ℝ) + 1) ≤ (cost r₁ r₂ (e i) + r₁ + r₂) ^ 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * r₁ * r₂)).mp hcard
    push_cast at hh
    nlinarith only [hh]
  have hh := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)] at hh
  linarith only [hh]

theorem finite_set_cost_lower (S : Finset (ℕ × ℕ)) (r₁ r₂ : ℝ)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) :
    (2 / 3 : ℝ) * S.card * Real.sqrt (2 * r₁ * r₂ * S.card) -
      (r₁ + r₂) * S.card ≤ ∑ p ∈ S, cost r₁ r₂ p := by
  obtain ⟨e, he, himage, hmono⟩ := sorted_enumeration S r₁ r₂
  have hsum := sum_le_sum (s := (univ : Finset (Fin S.card)))
    (fun i _ ↦ sorted_point_lower S.card e he r₁ r₂ hr₁ hr₂ hmono i)
  rw [sum_sub_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  have heq : (∑ i : Fin S.card, cost r₁ r₂ (e i)) = ∑ p ∈ S, cost r₁ r₂ p := by
    calc
      _ = ∑ p ∈ univ.image e, cost r₁ r₂ p := (sum_image (fun i _ j _ hij ↦ he hij)).symm
      _ = _ := congrArg (fun T : Finset (ℕ × ℕ) ↦ ∑ p ∈ T, cost r₁ r₂ p) himage
  rw [heq] at hsum
  have hsqrt : (2 / 3 : ℝ) * S.card * Real.sqrt S.card ≤
      ∑ i : Fin S.card, Real.sqrt ((i.val : ℝ) + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ Real.sqrt ((i : ℝ) + 1))]
    exact sum_sqrt_lower S.card
  have hm := mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg (2 * r₁ * r₂))
  rw [Real.sqrt_mul (by positivity)]
  nlinarith only [hsum, hm]

end PaperP1.WeightedLatticeCost
