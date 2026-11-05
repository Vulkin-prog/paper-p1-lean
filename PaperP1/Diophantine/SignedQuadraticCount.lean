module

public import PaperP1.Diophantine.UniformQuadraticCount
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Uniform quadratic counting with all coordinate signs and axis points

The internally proved positive count is used with its actual parameters.
No nonsquare or primitivity restriction is imposed on the final population.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedQuadraticCount

open Finset Filter PaperP1.PellInput

def absPair (z : ℤ × ℤ) : ℤ × ℤ := (|z.1|, |z.2|)

theorem absPair_fibre_card (S : Finset (ℤ × ℤ)) (t : ℤ × ℤ) :
    (S.filter (fun z ↦ absPair z = t)).card ≤ 4 := by
  have hsub : S.filter (fun z ↦ absPair z = t) ⊆ ({t.1, -t.1} ×ˢ {t.2, -t.2}) := by
    intro z hz
    have he := (mem_filter.mp hz).2
    have hx : |z.1| = t.1 := congrArg Prod.fst he
    have hy : |z.2| = t.2 := congrArg Prod.snd he
    have hx2 : z.1 ^ 2 = t.1 ^ 2 := by rw [← sq_abs z.1, hx]
    have hy2 : z.2 ^ 2 = t.2 ^ 2 := by rw [← sq_abs z.2, hy]
    exact mem_product.mpr ⟨by
      simpa only [mem_insert, mem_singleton] using eq_or_eq_neg_of_sq_eq_sq z.1 t.1 hx2, by
      simpa only [mem_insert, mem_singleton] using eq_or_eq_neg_of_sq_eq_sq z.2 t.2 hy2⟩
  exact (card_le_card hsub).trans (by
    rw [card_product]
    exact Nat.mul_le_mul card_le_two card_le_two)

theorem absPair_card (S : Finset (ℤ × ℤ)) : S.card ≤ 4 * (S.image absPair).card := by
  calc
    S.card = ∑ t ∈ S.image absPair, (S.filter (fun z ↦ absPair z = t)).card :=
      card_eq_sum_card_image absPair S
    _ ≤ ∑ _t ∈ S.image absPair, 4 := sum_le_sum (fun t _ht ↦ absPair_fibre_card S t)
    _ = _ := by simp [Nat.mul_comm]

theorem first_axis_card (A C : ℕ) (e : ℤ) (hC : 0 < C) (S : Finset (ℤ × ℤ))
    (hS : ∀ z ∈ S, pellEquation A C e z ∧ z.1 = 0) : S.card ≤ 2 := by
  by_cases hempty : S = ∅
  · simp [hempty]
  obtain ⟨z₀, hz₀⟩ := nonempty_iff_ne_empty.mpr hempty
  have hCne : (C : ℤ) ≠ 0 := by exact_mod_cast hC.ne'
  have hsub : S ⊆ {(0, z₀.2), (0, -z₀.2)} := by
    intro z hz
    have hzero := (hS z hz).2
    have heq := (hS z hz).1
    have heq₀ := (hS z₀ hz₀).1
    dsimp only [pellEquation] at heq heq₀
    rw [hzero] at heq
    rw [(hS z₀ hz₀).2] at heq₀
    have hsquare : z.2 ^ 2 = z₀.2 ^ 2 := mul_left_cancel₀ hCne (by nlinarith)
    rcases eq_or_eq_neg_of_sq_eq_sq z.2 z₀.2 hsquare with hh | hh
    · exact mem_insert.mpr (Or.inl (Prod.ext hzero hh))
    · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (Prod.ext hzero hh)))
  exact (card_le_card hsub).trans card_le_two

theorem second_axis_card (A C : ℕ) (e : ℤ) (hA : 0 < A) (S : Finset (ℤ × ℤ))
    (hS : ∀ z ∈ S, pellEquation A C e z ∧ z.2 = 0) : S.card ≤ 2 := by
  by_cases hempty : S = ∅
  · simp [hempty]
  obtain ⟨z₀, hz₀⟩ := nonempty_iff_ne_empty.mpr hempty
  have hAne : (A : ℤ) ≠ 0 := by exact_mod_cast hA.ne'
  have hsub : S ⊆ {(z₀.1, 0), (-z₀.1, 0)} := by
    intro z hz
    have hzero := (hS z hz).2
    have heq := (hS z hz).1
    have heq₀ := (hS z₀ hz₀).1
    dsimp only [pellEquation] at heq heq₀
    rw [hzero] at heq
    rw [(hS z₀ hz₀).2] at heq₀
    have hsquare : z.1 ^ 2 = z₀.1 ^ 2 := mul_left_cancel₀ hAne (by nlinarith)
    rcases eq_or_eq_neg_of_sq_eq_sq z.1 z₀.1 hsquare with hh | hh
    · exact mem_insert.mpr (Or.inl (Prod.ext hh hzero))
    · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (Prod.ext hh hzero)))
  exact (card_le_card hsub).trans card_le_two

theorem signed_count_le_rpow_eventually (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A C H : ℕ, ∀ e : ℤ,
      0 < A → 0 < C → e ≠ 0 → A ≤ N ^ K → C ≤ N ^ K →
      H ≤ N ^ K → e.natAbs ≤ N ^ K → HasAtMostSolutionsReal (pellBox A C e H) ((N : ℝ) ^ ε) := by
  obtain ⟨Nq, hq⟩ := UniformQuadraticCount.positive_count_le_rpow_eventually K (ε / 2) (by positivity)
  have ht := ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < ε / 2)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop (8 : ℝ))
  obtain ⟨Nc, hc⟩ := eventually_atTop.mp ht
  refine ⟨max 2 (max Nq Nc), ?_⟩
  intro N hN A C H e hA hC he hAN hCN hHN heN S hS
  let U := S.filter (fun z ↦ z.1 ≠ 0 ∧ z.2 ≠ 0)
  let X := S.filter (fun z ↦ z.1 = 0)
  let Y := S.filter (fun z ↦ z.2 = 0)
  have habs := hq N (by omega) A C H e hA hC he hAN hCN hHN heN (U.image absPair) (by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    obtain ⟨hwS, hnonzero⟩ := mem_filter.mp hw
    obtain ⟨heq, hx, hy⟩ := hS w hwS
    refine ⟨⟨?_, ?_, ?_⟩, abs_pos.mpr hnonzero.1, abs_pos.mpr hnonzero.2⟩
    · simpa only [pellEquation, absPair, sq_abs] using heq
    · simpa only [absPair, Int.natAbs_abs] using hx
    · simpa only [absPair, Int.natAbs_abs] using hy)
  have hU : (U.card : ℝ) ≤ 4 * (N : ℝ) ^ (ε / 2) := by
    have hh : (U.card : ℝ) ≤ 4 * ((U.image absPair).card : ℝ) := by exact_mod_cast absPair_card U
    exact hh.trans (mul_le_mul_of_nonneg_left habs (by norm_num))
  have hX : X.card ≤ 2 := first_axis_card A C e hC X (by
    intro z hz
    exact ⟨(hS z (mem_filter.mp hz).1).1, (mem_filter.mp hz).2⟩)
  have hY : Y.card ≤ 2 := second_axis_card A C e hA Y (by
    intro z hz
    exact ⟨(hS z (mem_filter.mp hz).1).1, (mem_filter.mp hz).2⟩)
  have hsub : S ⊆ U ∪ (X ∪ Y) := by
    intro z hz
    by_cases hx : z.1 = 0
    · exact mem_union_right U (mem_union_left Y (mem_filter.mpr ⟨hz, hx⟩))
    by_cases hy : z.2 = 0
    · exact mem_union_right U (mem_union_right X (mem_filter.mpr ⟨hz, hy⟩))
    exact mem_union_left _ (mem_filter.mpr ⟨hz, hx, hy⟩)
  have hcardN : S.card ≤ U.card + 4 := by
    have hh := (card_le_card hsub).trans (card_union_le U (X ∪ Y))
    have hh' := card_union_le X Y
    omega
  have hcardR : (S.card : ℝ) ≤ (U.card : ℝ) + 4 := by exact_mod_cast hcardN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpow : (1 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := Real.one_le_rpow
    (by exact_mod_cast (show 1 ≤ N by omega)) (by positivity)
  have hconstant : (8 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := hc N (by omega)
  calc
    (S.card : ℝ) ≤ 4 * (N : ℝ) ^ (ε / 2) + 4 := by linarith
    _ ≤ 8 * (N : ℝ) ^ (ε / 2) := by nlinarith
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hNp.le _)
    _ = _ := by rw [← Real.rpow_add hNp]; congr 1; ring

theorem generalized_count_le_rpow_eventually (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ D H : ℕ, ∀ m : ℤ,
      0 < D → m ≠ 0 → D ≤ N ^ K → H ≤ N ^ K → m.natAbs ≤ N ^ K →
        HasAtMostSolutionsReal (generalizedPellBox D m H) ((N : ℝ) ^ ε) := by
  obtain ⟨N₀, hN₀⟩ := signed_count_le_rpow_eventually K ε hε
  refine ⟨max 1 N₀, ?_⟩
  intro N hN D H m hD hm hDN hHN hmN S hS
  apply hN₀ N (by omega) 1 D H m (by decide) hD hm
    (Nat.one_le_pow _ _ (by omega)) hDN hHN hmN S
  intro z hz
  simpa only [pellBox, pellEquation, generalizedPellBox, Nat.cast_one, one_mul] using hS z hz

end PaperP1.SignedQuadraticCount
