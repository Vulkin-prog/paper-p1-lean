module

public import PaperP1.Model.PrivatePrimeForcing
public import PaperP1.Arithmetic.ReciprocalOddPivots
public import PaperP1.Combinatorics.IntervalMultiples
public import Mathlib.Data.Nat.Cast.Order.Field

/-! # Directed forcing footprints and the actual reciprocal-pivot sum

The estimates count directed source--target possibilities. A source pivot
may have arbitrary odd valuation and targets need not be independent.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateDirectedFootprint

open Finset PaperP1.Model PaperP1.Arithmetic PaperP1.PrivatePrimeForcing
  PaperP1.IntervalMultiples PaperP1.OddPrimePivot PaperP1.ReciprocalOddPivots

local instance privateDirectedFootprintDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

def hits (U N p b : ℕ) : Finset ℕ := (Ico U (U + N)).filter fun k ↦ p ∣ k + b

theorem hits_card (U N p b : ℕ) : (hits U N p b).card ≤ N / p + 1 := by
  have hi : (hits U N p b).card ≤
      ((Ico (U + b) (U + b + N)).filter fun k ↦ p ∣ k).card := by
    apply card_le_card_of_injOn (fun k ↦ k + b)
    · intro k hk
      obtain ⟨hk, hdiv⟩ := mem_filter.mp hk
      obtain ⟨hlo, hhi⟩ := mem_Ico.mp hk
      change k + b ∈ (Ico (U + b) (U + b + N)).filter (fun n ↦ p ∣ n)
      exact mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, hdiv⟩
    · intro k _ l _ h
      change k + b = l + b at h
      omega
  exact hi.trans (card_multiples_interval_le (U + b) N p)

theorem footprint_cover {M : ℕ} {ι : Type*} [Fintype ι]
    (U N Q : ℕ) (q : ι → PrimeUpTo M) :
    directedFootprint (Ico U (U + N)) Q q ⊆
      (univ : Finset ι).biUnion fun a ↦ (univ : Finset (Fin (Q + 1))).biUnion fun b ↦
        hits U N (q a).val.val b.val := by
  intro k hk
  obtain ⟨hk, a, b, hd⟩ := mem_filter.mp hk
  exact mem_biUnion.mpr ⟨a, mem_univ _, mem_biUnion.mpr
    ⟨b, mem_univ _, mem_filter.mpr ⟨hk, hd⟩⟩⟩

theorem footprint_card {M : ℕ} {ι : Type*} [Fintype ι]
    (U N Q : ℕ) (q : ι → PrimeUpTo M) :
    (directedFootprint (Ico U (U + N)) Q q).card ≤
      ∑ a, ∑ _b : Fin (Q + 1), (N / (q a).val.val + 1) := by
  calc
    _ ≤ ((univ : Finset ι).biUnion fun a ↦
        (univ : Finset (Fin (Q + 1))).biUnion fun b ↦ hits U N (q a).val.val b.val).card :=
      card_le_card (footprint_cover U N Q q)
    _ ≤ ∑ a, ((univ : Finset (Fin (Q + 1))).biUnion fun b ↦
        hits U N (q a).val.val b.val).card := card_biUnion_le
    _ ≤ ∑ a, ∑ b : Fin (Q + 1), (hits U N (q a).val.val b.val).card :=
      sum_le_sum fun _ _ ↦ card_biUnion_le
    _ ≤ _ := sum_le_sum fun a _ ↦ sum_le_sum fun b _ ↦ hits_card U N _ b.val

theorem footprint_card_real {M : ℕ} {ι : Type*} [Fintype ι]
    (U N Q : ℕ) (q : ι → PrimeUpTo M) :
    ((directedFootprint (Ico U (U + N)) Q q).card : ℝ) ≤
      (Q + 1 : ℝ) * ((N : ℝ) * (∑ a, 1 / ((q a).val.val : ℝ)) + Fintype.card ι) := by
  have hb : ((directedFootprint (Ico U (U + N)) Q q).card : ℝ) ≤
      ∑ a, ∑ _b : Fin (Q + 1), ((N / (q a).val.val : ℕ) + 1 : ℝ) := by
    exact_mod_cast footprint_card U N Q q
  calc
    _ ≤ ∑ a, ∑ _b : Fin (Q + 1), ((N / (q a).val.val : ℕ) + 1 : ℝ) := hb
    _ ≤ ∑ a, ∑ _b : Fin (Q + 1), ((N : ℝ) / (q a).val.val + 1) := by
      apply sum_le_sum
      intro a _
      apply sum_le_sum
      intro _ _
      have h : ((N / (q a).val.val : ℕ) : ℝ) ≤ (N : ℝ) / (q a).val.val := Nat.cast_div_le
      linarith only [h]
    _ = _ := by
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one, mul_add, sum_add_distrib, ← mul_sum, div_eq_mul_inv, one_mul]
      ring

theorem shifted_pivot_sum_le (J : Finset ℕ) (X b : ℕ)
    (hJ : ∀ j ∈ J, j + b ∈ Icc 1 X) :
    (∑ j ∈ J, 1 / (largestOddPrime (j + b) : ℝ)) ≤ pivotSum X := by
  unfold pivotSum
  apply sum_le_sum_of_injOn (fun j ↦ j + b)
  · intro j _ k _ h
    change j + b = k + b at h
    omega
  · intro n hn
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hn
    exact hJ j hj
  · intro _ _
    exact le_rfl
  · intro _ _ _
    positivity

theorem word_pivot_sum_le (J : Finset ℕ) (X B : ℕ)
    (hJ : ∀ j ∈ J, ∀ a : Fin B, j + a.val ∈ Icc 1 X) :
    (∑ j ∈ J, ∑ a : Fin B, 1 / (largestOddPrime (j + a.val) : ℝ)) ≤
      (B : ℝ) * pivotSum X := by
  rw [sum_comm]
  calc
    _ ≤ ∑ a : Fin B, pivotSum X :=
      sum_le_sum fun a _ ↦ shifted_pivot_sum_le J X a.val (fun j hj ↦ hJ j hj a)
    _ = _ := by simp

/-- The literal arithmetic ledger used before any reciprocal-pivot asymptotic. -/
theorem total_footprint_bound {M B : ℕ} (J : Finset ℕ) (U N Q X : ℕ)
    (q : ℕ → Fin B → PrimeUpTo M)
    (hq : ∀ j ∈ J, ∀ a, (q j a).val.val = largestOddPrime (j + a.val))
    (hJ : ∀ j ∈ J, ∀ a : Fin B, j + a.val ∈ Icc 1 X) :
    (∑ j ∈ J, ((directedFootprint (Ico U (U + N)) Q (q j)).card : ℝ)) ≤
      (Q + 1 : ℝ) * ((N : ℝ) * B * pivotSum X + (J.card : ℝ) * B) := by
  calc
    _ ≤ ∑ j ∈ J, (Q + 1 : ℝ) *
        ((N : ℝ) * (∑ a : Fin B, 1 / (largestOddPrime (j + a.val) : ℝ)) + B) := by
      apply sum_le_sum
      intro j hj
      have h := footprint_card_real U N Q (q j)
      simpa only [hq j hj, Fintype.card_fin] using h
    _ = (Q + 1 : ℝ) * ((N : ℝ) *
        (∑ j ∈ J, ∑ a : Fin B, 1 / (largestOddPrime (j + a.val) : ℝ)) + (J.card : ℝ) * B) := by
      simp only [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      have h := word_pivot_sum_le J X B hJ
      have h' := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ N)
      have h'' := mul_le_mul_of_nonneg_left (add_le_add_right h' ((J.card : ℝ) * B))
        (by positivity : (0 : ℝ) ≤ Q + 1)
      simpa only [mul_assoc, add_comm] using h''

end PaperP1.PrivateDirectedFootprint
