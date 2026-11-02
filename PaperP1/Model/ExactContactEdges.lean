module

public import PaperP1.Model.FullRankPrescriptions
public import PaperP1.Combinatorics.ClosePairs

/-! # Literal exact-contact edges and their regular-union lower mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExactContactEdges

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def starts (N L : ℕ) : Finset ℕ := (dyadicBlock N).filter fun x ↦ x + L ∈ dyadicBlock N

def edges (N L : ℕ) : Finset (Finset ℕ) := (starts N L).image fun x ↦ {x, x + L}

def regularUnionStarts (N L : ℕ) : Finset ℕ := starts N L \ RegularStarts.irregularStarts N (2 * L)

def mass (N L : ℕ) : ℝ := ∑ e ∈ edges N L, infiniteJointMoment L e

theorem map_injective (L : ℕ) : Function.Injective (fun x : ℕ ↦ ({x, x + L} : Finset ℕ)) := by
  intro x y heq
  change ({x, x + L} : Finset ℕ) = {y, y + L} at heq
  have hx : x ∈ ({y, y + L} : Finset ℕ) := by rw [← heq]; simp
  have hy : y ∈ ({x, x + L} : Finset ℕ) := by rw [heq]; simp
  simp only [mem_insert, mem_singleton] at hx hy
  omega

theorem subset_pairs (N L : ℕ) (hL : 0 < L) : edges N L ⊆ (dyadicBlock N).powersetCard 2 := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := mem_image.mp he
  obtain ⟨hx, hy⟩ := mem_filter.mp hx
  exact mem_powersetCard.mpr ⟨insert_subset_iff.mpr ⟨hx, singleton_subset_iff.mpr hy⟩,
    by
      have hne : x ≠ x + L := by omega
      exact card_pair_eq_two_iff.mpr hne⟩

theorem subset_close (N L : ℕ) (hL : 0 < L) : edges N L ⊆ ClosePairs.pairs (dyadicBlock N) L := by
  intro e he
  have hep := subset_pairs N L hL he
  obtain ⟨x, hx, rfl⟩ := mem_image.mp he
  exact mem_filter.mpr ⟨hep, x, mem_insert_self _ _, x + L, by simp, by omega, le_rfl⟩

theorem mass_eq (N L : ℕ) : mass N L = ∑ x ∈ starts N L, infiniteJointMoment L {x, x + L} := by
  rw [mass, edges, sum_image (map_injective L).injOn]

theorem starts_eq_interval {N L : ℕ} (hLN : L ≤ N) : starts N L = Ico N (2 * N - L) := by
  ext x
  simp only [starts, mem_filter, dyadicBlock, mem_Ico]
  omega

theorem starts_card {N L : ℕ} (hLN : L ≤ N) : (starts N L).card = N - L := by
  rw [starts_eq_interval hLN, Nat.card_Ico]
  omega

theorem regular_union_count {N L : ℕ} (hLN : L ≤ N) :
    N - L ≤ (regularUnionStarts N L).card + (RegularStarts.irregularStarts N (2 * L)).card := by
  have hc := card_sdiff_add_card_inter (starts N L) (RegularStarts.irregularStarts N (2 * L))
  have hi := card_le_card (inter_subset_right : starts N L ∩ RegularStarts.irregularStarts N (2 * L) ⊆ _)
  rw [starts_card hLN] at hc
  dsimp [regularUnionStarts]
  omega

theorem regular_union_mem {N L x : ℕ} (hx : x ∈ regularUnionStarts N L) :
    x ∈ RegularStarts.regularStarts N (2 * L) := by
  obtain ⟨hx, hnot⟩ := mem_sdiff.mp hx
  have hxN := (mem_filter.mp hx).1
  by_contra hreg
  exact hnot (mem_sdiff.mpr ⟨hxN, hreg⟩)

theorem mass_lower {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    ((regularUnionStarts N L).card : ℝ) * (2 ^ (2 * L) : ℝ)⁻¹ ≤ mass N L := by
  rw [mass_eq]
  calc
    _ = ∑ x ∈ regularUnionStarts N L, infiniteJointMoment L {x, x + L} := by
      have heq : (∑ x ∈ regularUnionStarts N L, infiniteJointMoment L {x, x + L}) =
          ∑ _x ∈ regularUnionStarts N L, (2 ^ (2 * L) : ℝ)⁻¹ := by
        apply sum_congr rfl
        intro x hx
        have hxN := (mem_filter.mp (mem_sdiff.mp hx).1).1
        exact FullRankPrescriptions.actual_contact_on_regular_union
          (by have h := (mem_Ico.mp hxN).1; omega) hL (regular_union_mem hx)
      rw [heq, sum_const, nsmul_eq_mul]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (show regularUnionStarts N L ⊆ starts N L from fun _ h ↦ (mem_sdiff.mp h).1) (fun x _ _ ↦ infiniteJointMoment_nonneg L _)

end PaperP1.ExactContactEdges
