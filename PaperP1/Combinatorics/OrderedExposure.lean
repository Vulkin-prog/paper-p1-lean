module

public import PaperP1.Combinatorics.ExposureOrder
public import Mathlib.Data.Fintype.EquivFin

/-! # Actual finite exposure orders with a prescribed last index -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrderedExposure

open Finset PaperP1.ExposureWeights PaperP1.ExposureOrder

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
theorem exists_rank_last [Fintype ι] (last : ι) :
    ∃ rank : ι → ℕ, Function.Injective rank ∧ ∀ i, rank i ≤ rank last := by
  have hv : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨last⟩
  let top : Fin (Fintype.card ι) := ⟨Fintype.card ι - 1, by omega⟩
  let e := (Fintype.equivFin ι).trans (Equiv.swap ((Fintype.equivFin ι) last) top)
  refine ⟨fun i ↦ (e i).val, ?_, ?_⟩
  · intro i j hij
    exact e.injective (Fin.ext hij)
  · intro i
    have hlast : e last = top := by simp [e]
    change (e i).val ≤ (e last).val
    rw [hlast]
    have hi := (e i).isLt
    change (e i).val ≤ Fintype.card ι - 1
    omega

omit [DecidableEq ι] in
theorem exists_equiv_last [Fintype ι] (last : ι) :
    ∃ e : ι ≃ Fin (Fintype.card ι), (e last).val = Fintype.card ι - 1 := by
  have hv : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨last⟩
  let top : Fin (Fintype.card ι) := ⟨Fintype.card ι - 1, by omega⟩
  let e := (Fintype.equivFin ι).trans (Equiv.swap ((Fintype.equivFin ι) last) top)
  refine ⟨e, ?_⟩
  have he : e last = top := by simp [e]
  exact congrArg Fin.val he

def firstByRank (rank : ι → ℕ) (fallback : ι) (S : Finset ι) : ι :=
  if hS : S.Nonempty then Classical.choose (S.exists_min_image rank hS) else fallback

omit [DecidableEq ι] in
theorem firstByRank_mem (rank : ι → ℕ) (fallback : ι) (S : Finset ι) (hS : S.Nonempty) :
    firstByRank rank fallback S ∈ S := by
  unfold firstByRank
  rw [dite_eq_left hS]
  exact (Classical.choose_spec (S.exists_min_image rank hS)).1

omit [DecidableEq ι] in
theorem firstByRank_min (rank : ι → ℕ) (fallback : ι) (S : Finset ι)
    (hS : S.Nonempty) (i : ι) (hi : i ∈ S) :
    rank (firstByRank rank fallback S) ≤ rank i := by
  unfold firstByRank
  rw [dite_eq_left hS]
  exact (Classical.choose_spec (S.exists_min_image rank hS)).2 i hi

omit [DecidableEq ι] in
theorem firstByRank_ne_last (rank : ι → ℕ) (hrank : Function.Injective rank)
    (last : ι) (hlast : ∀ i, rank i ≤ rank last) (S : Finset ι) (hS : 2 ≤ S.card) :
    firstByRank rank last S ≠ last := by
  classical
  have hSne : S.Nonempty := card_pos.mp (by omega)
  intro heq
  have hsub : S ⊆ {last} := by
    intro i hi
    have hlo := firstByRank_min rank last S hSne i hi
    rw [heq] at hlo
    exact mem_singleton.mpr (hrank (le_antisymm (hlast i) hlo))
  have hc := card_le_card hsub
  simp only [card_singleton] at hc
  omega

omit [DecidableEq ι] in
theorem earlier_iff_ne_first (rank : ι → ℕ) (hrank : Function.Injective rank)
    (fallback : ι) (S : Finset ι) (i : ι) (hi : i ∈ S) :
    (∃ j ∈ S, rank j < rank i) ↔ firstByRank rank fallback S ≠ i := by
  have hS : S.Nonempty := ⟨i, hi⟩
  constructor
  · rintro ⟨j, hj, hji⟩ heq
    have hmin := firstByRank_min rank fallback S hS j hj
    rw [heq] at hmin
    omega
  · intro hne
    refine ⟨firstByRank rank fallback S, firstByRank_mem rank fallback S hS, ?_⟩
    exact lt_of_le_of_ne (firstByRank_min rank fallback S hS i hi) (fun heq ↦ hne (hrank heq))

theorem prescribedWeight_earlier (H : Finset (Finset ι)) (w : Finset ι → ℝ)
    (rank : ι → ℕ) (hrank : Function.Injective rank) (fallback : ι)
    (hH : ∀ S ∈ H, S.Nonempty) (i : ι) :
    prescribedWeight H w (firstByRank rank fallback) i =
      ∑ S ∈ H.filter (fun S ↦ i ∈ S ∧ ∃ j ∈ S, rank j < rank i), w S := by
  rw [prescribedWeight_filter H w (firstByRank rank fallback)
    (fun S hS ↦ firstByRank_mem rank fallback S (hH S hS))]
  apply sum_congr
  · apply filter_congr
    intro S _
    constructor
    · rintro ⟨hi, hne⟩
      exact ⟨hi, (earlier_iff_ne_first rank hrank fallback S i hi).mpr hne⟩
    · rintro ⟨hi, hearlier⟩
      exact ⟨hi, (earlier_iff_ne_first rank hrank fallback S i hi).mp hearlier⟩
  · intro _ _
    rfl

theorem exists_exposure_exponent_le [Fintype ι] [Nonempty ι]
    (H : Finset (Finset ι)) (w : Finset ι → ℝ)
    (hw : ∀ S ∈ H, 0 ≤ w S) (hH : ∀ S ∈ H, 2 ≤ S.card)
    (d E : ℝ) (hd : 0 < d)
    (hbudget : (∑ S ∈ H, (S.card : ℝ) * w S) ≤ Fintype.card ι * d + E) :
    ∃ (last : ι) (rank : ι → ℕ), Function.Injective rank ∧ (∀ i, rank i ≤ rank last) ∧
      ((Fintype.card ι : ℝ) - 1) / 2 +
        (∑ i ∈ univ.erase last,
          (degree H w i / 2 - prescribedWeight H w (firstByRank rank last) i)) / d ≤
        Fintype.card ι / 2 + E / (2 * d * Fintype.card ι) := by
  obtain ⟨last, hlast⟩ := exists_last_exponent_le H w hw hH d E hd hbudget
  obtain ⟨rank, hrank, hmax⟩ := exists_rank_last last
  refine ⟨last, rank, hrank, hmax, ?_⟩
  rw [exposure_identity H w (firstByRank rank last) last
    (fun S hS ↦ firstByRank_ne_last rank hrank last hmax S (hH S hS))]
  exact hlast

end PaperP1.OrderedExposure
