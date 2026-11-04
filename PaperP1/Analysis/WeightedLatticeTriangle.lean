module

public import PaperP1.Analysis.DeterminantChartBound
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.BigOperators.Intervals

/-! # Uniform counting of distinct lattice monomials below a weighted threshold -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedLatticeTriangle

open Finset

def cost (r₁ r₂ : ℝ) (p : ℕ × ℕ) : ℝ := r₁ * p.1 + r₂ * p.2

theorem natural_card_bound (S : Finset ℕ) (T : ℝ) (hT : 0 ≤ T)
    (hS : ∀ k ∈ S, (k : ℝ) ≤ T) : (S.card : ℝ) ≤ T + 1 := by
  have hs : S ⊆ range (⌊T⌋₊ + 1) := by
    intro k hk
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor (hS k hk)))
  have hc := card_le_card hs
  rw [card_range] at hc
  calc
    (S.card : ℝ) ≤ ((⌊T⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hc
    _ ≤ T + 1 := by push_cast; linarith only [Nat.floor_le hT]

theorem fiber_card_bound (S : Finset (ℕ × ℕ)) (r₁ r₂ T : ℝ) (hr₂ : 0 < r₂)
    (hS : ∀ p ∈ S, cost r₁ r₂ p ≤ T) (a : ℕ) (ha : r₁ * a ≤ T) :
    ((S.filter (fun p ↦ p.1 = a)).card : ℝ) ≤ (T - r₁ * a) / r₂ + 1 := by
  let F := S.filter (fun p ↦ p.1 = a)
  have hi : Set.InjOn Prod.snd (F : Set (ℕ × ℕ)) := by
    intro p hp q hq heq
    exact Prod.ext ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm) heq
  have hc := card_image_of_injOn hi
  rw [← hc]
  apply natural_card_bound _ _ (div_nonneg (sub_nonneg.mpr ha) hr₂.le)
  intro b hb
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hb
  have hpS := (mem_filter.mp hp).1
  have hpa := (mem_filter.mp hp).2
  apply (le_div_iff₀ hr₂).mpr
  have hh := hS p hpS
  unfold cost at hh
  rw [hpa] at hh
  linarith only [hh]

theorem sum_first_coordinates (m : ℕ) :
    (∑ a ∈ range (m + 1), (a : ℝ)) = (m : ℝ) * (m + 1) / 2 := by
  have h := congrArg (fun n : ℕ ↦ (n : ℝ)) (sum_range_id_mul_two (m + 1))
  push_cast at h
  linarith only [h]

theorem quadratic_bound {r₁ r₂ T x : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hT : 0 ≤ T) :
    x * ((T - r₁ * (x - 1) / 2) / r₂ + 1) ≤
      (T + r₁ + r₂) ^ 2 / (2 * r₁ * r₂) := by
  apply (le_div_iff₀ (by positivity : 0 < 2 * r₁ * r₂)).mpr
  have hs := sq_nonneg (r₁ * x - (T + r₂ + r₁ / 2))
  have hbase : 0 ≤ (T + r₁ + r₂) ^ 2 - (T + r₂ + r₁ / 2) ^ 2 := by
    nlinarith only [hT, hr₁, hr₂]
  have heq : x * ((T - r₁ * (x - 1) / 2) / r₂ + 1) * (2 * r₁ * r₂) =
      2 * r₁ * x * (T + r₂ + r₁ / 2) - (r₁ * x) ^ 2 := by
    field_simp
    ring
  rw [heq]
  nlinarith only [hs, hbase]

theorem triangle_card_bound (S : Finset (ℕ × ℕ)) (r₁ r₂ T : ℝ)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hT : 0 ≤ T)
    (hS : ∀ p ∈ S, cost r₁ r₂ p ≤ T) :
    (S.card : ℝ) ≤ (T + r₁ + r₂) ^ 2 / (2 * r₁ * r₂) := by
  let m := ⌊T / r₁⌋₊
  have hmaps : (S : Set (ℕ × ℕ)).MapsTo Prod.fst (range (m + 1)) := by
    intro p hp
    apply mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.le_floor
    apply (le_div_iff₀ hr₁).mpr
    have hh := hS p hp
    unfold cost at hh
    have hz : 0 ≤ r₂ * (p.2 : ℝ) := mul_nonneg hr₂.le (Nat.cast_nonneg _)
    linarith only [hh, hz]
  have hcard := card_eq_sum_card_fiberwise hmaps
  have hm : (m : ℝ) ≤ T / r₁ := Nat.floor_le (div_nonneg hT hr₁.le)
  have hrow (a : ℕ) (ha : a ∈ range (m + 1)) : r₁ * a ≤ T := by
    have han : a ≤ m := by simpa only [mem_range, Nat.lt_succ_iff] using ha
    have hle : (a : ℝ) ≤ T / r₁ := (by exact_mod_cast han : (a : ℝ) ≤ m).trans hm
    simpa only [mul_comm] using (le_div_iff₀ hr₁).mp hle
  have hsum : (S.card : ℝ) ≤ ∑ a ∈ range (m + 1), ((T - r₁ * a) / r₂ + 1) := by
    rw [hcard, Nat.cast_sum]
    apply sum_le_sum
    intro a ha
    exact fiber_card_bound S r₁ r₂ T hr₂ hS a (hrow a ha)
  have hformula : (∑ a ∈ range (m + 1), ((T - r₁ * a) / r₂ + 1)) =
      ((m : ℝ) + 1) * ((T - r₁ * m / 2) / r₂ + 1) := by
    have hterm (a : ℕ) : (T - r₁ * a) / r₂ + 1 = (T / r₂ + 1) - (r₁ / r₂) * a := by ring
    simp_rw [hterm]
    rw [sum_sub_distrib, sum_const, ← mul_sum, sum_first_coordinates m]
    simp only [card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring
  rw [hformula] at hsum
  exact hsum.trans (by simpa only [add_sub_cancel_right] using
    (quadratic_bound (x := (m : ℝ) + 1) hr₁ hr₂ hT))

end PaperP1.WeightedLatticeTriangle
