module

public import PaperP1.Model.SignedCostEnvelope
public import PaperP1.Asymptotics.CriticalRawValueProfileUnderInputs

/-! # The actual finite signed forcing upper ledger on retained dyadic starts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedDyadicCostUpper

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.SignedPrivateField
  PaperP1.SignedPrivateDyadicField PaperP1.SignedCostEnvelope PaperP1.SignedMaximalFootprint
  PaperP1.ReciprocalOddPivots PaperP1.RawPairRelationRank

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def closeSites (J : Finset ℕ) (L E : ℕ) (j : J) : Finset J :=
  univ.filter fun k ↦ Close L E j.val k.val

theorem closeSites_card (J : Finset ℕ) (L E : ℕ) (j : J) :
    (closeSites J L E j).card ≤ 2 * (L + E + 2) := by
  have hh : (closeSites J L E j).card ≤
      (Ico (j.val - (L + E + 2)) (j.val + (L + E + 2))).card := by
    apply card_le_card_of_injOn (fun k : J ↦ k.val)
    · intro k hk
      have hc := (mem_filter.mp hk).2
      change k.val ∈ Ico (j.val - (L + E + 2)) (j.val + (L + E + 2))
      exact mem_Ico.mpr ⟨by dsimp [Close] at hc; omega, hc.2⟩
    · intro k _ l _ he
      exact Subtype.ext he
  exact hh.trans (by simp only [Nat.card_Ico]; omega)

theorem boundaries_subset {N L E : ℕ} (hN : 2 ≤ N) :
    retainedBoundaries N L E ⊆ Ico (N - 1) (N - 1 + N) := by
  intro j hj
  have hx := boundary_recover hN hj
  have hh := mem_Ico.mp (mem_filter.mp hx).1
  exact mem_Ico.mpr ⟨by omega, by omega⟩

theorem far_profile_le {N L E : ℕ} (hN : 2 ≤ N) :
    (∑ j : retainedBoundaries N L E, ∑ k : retainedBoundaries N L E,
      if Close L E j.val k.val then (0 : ℝ) else
        (2 ^ fullRank (j.val + 1) (k.val + 1) (L + E + 1) : ℝ) - 1) ≤
      CriticalRawValueProfileUnderInputs.mass N (L + E + 1) := by
  let J := retainedBoundaries N L E
  let F : Finset (J × J) := univ.filter fun p ↦ ¬ Close L E p.1.val p.2.val
  have he : (∑ j : J, ∑ k : J, if Close L E j.val k.val then (0 : ℝ) else
      (2 ^ fullRank (j.val + 1) (k.val + 1) (L + E + 1) : ℝ) - 1) =
      ∑ p ∈ F, ((2 ^ fullRank (p.1.val + 1) (p.2.val + 1) (L + E + 1) : ℝ) - 1) := by
    rw [show F = univ.filter (fun p : J × J ↦ ¬ Close L E p.1.val p.2.val) from rfl, sum_filter]
    simp only [ite_not, Fintype.sum_prod_type]
  rw [he]
  unfold CriticalRawValueProfileUnderInputs.mass
  apply sum_le_sum_of_injOn (fun p : J × J ↦ (p.1.val + 1, p.2.val + 1))
  · intro p _ q _ heq
    apply Prod.ext
    · apply Subtype.ext
      have := congrArg Prod.fst heq
      dsimp at this
      omega
    · apply Subtype.ext
      have := congrArg Prod.snd heq
      dsimp at this
      omega
  · intro p hp
    obtain ⟨jk, hjk, rfl⟩ := mem_image.mp hp
    have hn := (mem_filter.mp hjk).2
    have hj := (mem_filter.mp (boundary_recover hN jk.1.property)).1
    have hk := (mem_filter.mp (boundary_recover hN jk.2.property)).1
    exact (PairSeparation.mem_separatedHosts _ _ _).mpr ⟨hj, hk, by dsimp [Close] at hn; dsimp; omega⟩
  · intro _ _
    exact le_rfl
  · intro _ _ _
    exact sub_nonneg.mpr (one_le_pow₀ (by norm_num))

theorem finite_upper {N L E : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L) (hB : L + E + 2 ≤ N) :
    cost (data (E := E) hN hL) ≤ ((2 ^ L : ℝ)⁻¹) ^ 2 *
      ((N : ℝ) + 2 * (L + E + 2 : ℝ) *
        ((N : ℝ) * (L + E + 2) * pivotSum (3 * N) + (N : ℝ) * (L + E + 2)) +
          8 * N * (L + E + 2) + CriticalRawValueProfileUnderInputs.mass N (L + E + 1)) := by
  let J := retainedBoundaries N L E
  let D := data (E := E) hN hL
  have hJN : (J.card : ℝ) ≤ N := by exact_mod_cast boundaries_card N L E
  have hfoot := total_card_bound D (N - 1) N (3 * N) (boundaries_subset hN)
    (fun _ hj i ↦ boundary_vertices hN hB hj i)
  have hC (j : J) : ((closeSites J L E j).card : ℝ) ≤ 2 * (L + E + 2 : ℝ) := by
    have hh := closeSites_card J L E j
    exact_mod_cast hh
  have hclose : (∑ j : J, ((closeSites J L E j).card : ℝ)) ≤ 2 * N * (L + E + 2 : ℝ) := by
    calc
      _ ≤ ∑ _j : J, 2 * (L + E + 2 : ℝ) := sum_le_sum (fun j _ ↦ hC j)
      _ ≤ _ := by
        simp only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
        nlinarith only [mul_nonneg (sub_nonneg.mpr hJN) (by positivity : (0 : ℝ) ≤ L + E + 2)]
  have hdiag : (∑ j : J, ∑ k : J, if j = k then (1 : ℝ) else 0) = J.card := by simp
  have hhit (j : J) : (∑ k : J, if k ∈ siteFootprint D j then (1 : ℝ) else 0) =
      (siteFootprint D j).card := by
    rw [← sum_filter]
    rw [filter_mem_eq_inter, univ_inter]
    simp only [sum_const, nsmul_eq_mul, mul_one]
  have hcl (j : J) : (∑ k : J, if Close L E j.val k.val then (1 : ℝ) else 0) =
      (closeSites J L E j).card := by
    rw [← sum_filter]
    simp [closeSites]
  have hsplit : (∑ j : J, ∑ k : J, envelope D j k) =
      J.card + 2 * (∑ j : J, ((siteFootprint D j).card : ℝ)) +
        4 * (∑ j : J, ((closeSites J L E j).card : ℝ)) +
          (∑ j : J, ∑ k : J, if Close L E j.val k.val then (0 : ℝ) else
            (2 ^ fullRank (j.val + 1) (k.val + 1) (L + E + 1) : ℝ) - 1) := by
    simp only [envelope, sum_add_distrib, ← mul_sum, hdiag, hhit, hcl]
  have hsum : (∑ j : J, ∑ k : J, envelope D j k) ≤
      (N : ℝ) + 2 * (L + E + 2 : ℝ) *
        ((N : ℝ) * (L + E + 2) * pivotSum (3 * N) + (N : ℝ) * (L + E + 2)) +
          8 * N * (L + E + 2) + CriticalRawValueProfileUnderInputs.mass N (L + E + 1) := by
    rw [hsplit]
    have hf := far_profile_le (L := L) (E := E) hN
    have hcard := mul_nonneg (sub_nonneg.mpr hJN) (sq_nonneg (L + E + 2 : ℝ))
    nlinarith only [hfoot, hclose, hJN, hf, hcard]
  exact (cost_le_envelope D (by dsimp [pivotCutoff]; omega)).trans
    (mul_le_mul_of_nonneg_left hsum (sq_nonneg _))

theorem finite_upper_coarse {N L E : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L) (hB : L + E + 2 ≤ N) :
    cost (data (E := E) hN hL) ≤ ((2 ^ L : ℝ)⁻¹) ^ 2 *
      (12 * (N : ℝ) * (L + E + 2 : ℝ) ^ 2 * (pivotSum (3 * N) + 1) +
        CriticalRawValueProfileUnderInputs.mass N (L + E + 1)) := by
  let B : ℝ := L + E + 2
  have hB1 : 1 ≤ B := by dsimp [B]; have := Nat.cast_nonneg (α := ℝ) L; have := Nat.cast_nonneg (α := ℝ) E; linarith
  have hBs : B ≤ B ^ 2 := by nlinarith only [hB1]
  have hB2 : 1 ≤ B ^ 2 := one_le_pow₀ hB1
  have hNN : (0 : ℝ) ≤ N := by positivity
  have hN1 := mul_le_mul_of_nonneg_left hB2 hNN
  have hNB := mul_le_mul_of_nonneg_left hBs hNN
  have hK : 0 ≤ (N : ℝ) * B ^ 2 * pivotSum (3 * N) :=
    mul_nonneg (mul_nonneg hNN (sq_nonneg B)) (pivotSum_nonneg _)
  have hp : (N : ℝ) + 2 * B * ((N : ℝ) * B * pivotSum (3 * N) + (N : ℝ) * B) +
      8 * N * B + CriticalRawValueProfileUnderInputs.mass N (L + E + 1) ≤
      12 * (N : ℝ) * B ^ 2 * (pivotSum (3 * N) + 1) +
        CriticalRawValueProfileUnderInputs.mass N (L + E + 1) := by
    nlinarith only [hN1, hNB, hK]
  exact (finite_upper hN hL hB).trans (mul_le_mul_of_nonneg_left hp (sq_nonneg _))

end PaperP1.SignedDyadicCostUpper
