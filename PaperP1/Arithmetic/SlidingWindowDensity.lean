module

public import PaperP1.Model.ForcingExceptionalSets

/-! # A finite positive-density census of windows with two selected values

The actual boundary population is retained, including its shift by one. All
endpoint losses are explicit. The selected integer set can be arbitrary.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SlidingWindowDensity

open Finset ForcingExceptionalSets

def selectedIndices (j B : ℕ) (S : Finset ℕ) : Finset (Fin B) :=
  univ.filter fun i ↦ j + i.val ∈ S

def goodWindows (N B : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (boundaryBlock N).filter fun j ↦ 2 ≤ (selectedIndices j B S).card

def core (N B : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.filter fun n ↦ N + B ≤ n ∧ n + 2 ≤ 2 * N

theorem core_card_loss {N B : ℕ} {S : Finset ℕ} (hN : 2 ≤ N) (hS : S ⊆ Ico N (2 * N)) :
    S.card ≤ (core N B S).card + B + 2 := by
  have hcover : S ⊆ core N B S ∪ (Ico N (N + B) ∪ Ico (2 * N - 2) (2 * N)) := by
    intro n hn
    obtain ⟨hnN, hn2⟩ := mem_Ico.mp (hS hn)
    by_cases hc : N + B ≤ n ∧ n + 2 ≤ 2 * N
    · exact mem_union_left _ (mem_filter.mpr ⟨hn, hc⟩)
    · apply mem_union_right
      by_cases hl : n < N + B
      · exact mem_union_left _ (mem_Ico.mpr ⟨hnN, hl⟩)
      · exact mem_union_right _ (mem_Ico.mpr ⟨by omega, hn2⟩)
  have hh := (card_le_card hcover).trans (card_union_le _ _)
  have hu := card_union_le (Ico N (N + B)) (Ico (2 * N - 2) (2 * N))
  simp only [Nat.card_Ico] at hh hu
  omega

theorem offset_card_lower {N B : ℕ} {S : Finset ℕ} (hN : 2 ≤ N) (i : Fin B) :
    (core N B S).card ≤ ((boundaryBlock N).filter fun j ↦ j + i.val ∈ S).card := by
  apply card_le_card_of_injOn (fun n ↦ n - i.val)
  · intro n hn
    obtain ⟨hnS, hlow, hhigh⟩ := mem_filter.mp hn
    have hi := i.isLt
    apply mem_filter.mpr
    constructor
    · rw [boundaryBlock_eq_interval hN, mem_Ioc]
      change N - 2 < n - i.val ∧ n - i.val ≤ N - 2 + N
      omega
    · simpa only [Nat.sub_add_cancel (by omega : i.val ≤ n)] using hnS
  · intro n hn m hm he
    have hnl := (mem_filter.mp hn).2.1
    have hml := (mem_filter.mp hm).2.1
    have hi := i.isLt
    change n - i.val = m - i.val at he
    omega

theorem total_incidence_lower {N B : ℕ} {S : Finset ℕ} (hN : 2 ≤ N) :
    B * (core N B S).card ≤ ∑ j ∈ boundaryBlock N, (selectedIndices j B S).card := by
  calc
    _ = ∑ _i : Fin B, (core N B S).card := by simp
    _ ≤ ∑ i : Fin B, ((boundaryBlock N).filter fun j ↦ j + i.val ∈ S).card :=
      sum_le_sum (fun i _ ↦ offset_card_lower hN i)
    _ = ∑ i : Fin B, ∑ j ∈ boundaryBlock N, if j + i.val ∈ S then (1 : ℕ) else 0 := by
      simp only [card_eq_sum_ones, sum_filter]
    _ = ∑ j ∈ boundaryBlock N, ∑ i : Fin B, if j + i.val ∈ S then (1 : ℕ) else 0 := sum_comm
    _ = _ := by simp only [selectedIndices, card_eq_sum_ones, sum_filter]

theorem total_incidence_upper {N B : ℕ} {S : Finset ℕ} (hN : 2 ≤ N) :
    (∑ j ∈ boundaryBlock N, (selectedIndices j B S).card) ≤ N + B * (goodWindows N B S).card := by
  calc
    _ ≤ ∑ j ∈ boundaryBlock N, (1 + if 2 ≤ (selectedIndices j B S).card then B else 0) := by
      apply sum_le_sum
      intro j _
      have hh : (selectedIndices j B S).card ≤ B :=
        (card_le_card (filter_subset _ _)).trans_eq (by simp)
      split_ifs <;> omega
    _ = _ := by
      rw [sum_add_distrib, sum_const, boundaryBlock_card hN, nsmul_eq_mul, mul_one, ← sum_filter]
      simp [goodWindows, mul_comm]

theorem good_window_bound {N B : ℕ} {S : Finset ℕ} (hN : 2 ≤ N) (hS : S ⊆ Ico N (2 * N)) :
    B * S.card ≤ B * (B + 2) + N + B * (goodWindows N B S).card := by
  have hc := Nat.mul_le_mul_left B (core_card_loss (B := B) hN hS)
  have hi := (total_incidence_lower (S := S) (B := B) hN).trans (total_incidence_upper hN)
  nlinarith only [hc, hi]

theorem density_lower {N B : ℕ} {S : Finset ℕ} (hN : 2 ≤ N) (hB : 0 < B)
    (hS : S ⊆ Ico N (2 * N)) (δ : ℝ) (hfull : δ * (N : ℝ) ≤ S.card)
    (hlarge : 4 ≤ δ * B) (hshort : (B : ℝ) + 2 ≤ δ * N / 4) :
    δ / 2 * (N : ℝ) ≤ (goodWindows N B S).card := by
  have hb : (0 : ℝ) < B := by exact_mod_cast hB
  have hc : (B : ℝ) * S.card ≤ (B : ℝ) * (B + 2) + N + B * (goodWindows N B S).card := by
    exact_mod_cast good_window_bound hN hS
  have h1 := mul_le_mul_of_nonneg_left hfull hb.le
  have h2 := mul_le_mul_of_nonneg_left hshort hb.le
  have h3 := mul_le_mul_of_nonneg_right hlarge (Nat.cast_nonneg (α := ℝ) N)
  have hh : (B : ℝ) * (δ / 2 * N) ≤ B * (goodWindows N B S).card := by
    nlinarith only [hc, h1, h2, h3]
  exact (mul_le_mul_iff_right₀ hb).mp hh

end PaperP1.SlidingWindowDensity
