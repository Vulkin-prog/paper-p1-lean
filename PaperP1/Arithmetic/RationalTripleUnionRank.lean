module

public import PaperP1.Arithmetic.RationalTripleNormalizers
public import PaperP1.Combinatorics.ThreeUnionCard
public import PaperP1.Arithmetic.RationalTripleOverlap

/-! # Actual normalized-union ranks from the rational overlap density -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalTripleUnionRank

open Finset PaperP1.Arithmetic PaperP1.NormalizedWindowSets PaperP1.PrivateNormalizedFamilies
  PaperP1.RationalTripleNormalizers

theorem triple_intersection_count {u v w t L : ℕ} (hu : 2 ≤ u) (huv : u ≤ v) (hvw : v ≤ w)
    (ht : 1 ≤ t) (hL : 1 ≤ L) :
    (L - 1) / w + 1 ≤ ((values u v w t L 0 ∩ values u v w t L 1) ∩ values u v w t L 2).card := by
  have hw : 0 < w := by omega
  have hM : 0 < u * v * w := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hw
  let J := (range ((L - 1) / w + 1)).image fun m ↦ origin u v w t + (u * v * w) * m
  have hsub : J ⊆ (values u v w t L 0 ∩ values u v w t L 1) ∩ values u v w t L 2 := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
    have hwm : w * m ≤ L - 1 := by
      have hmle : m ≤ (L - 1) / w := by have hh := mem_range.mp hm; omega
      calc
        _ ≤ w * ((L - 1) / w) := Nat.mul_le_mul_left w hmle
        _ ≤ L - 1 := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
    have hmem (i : Fin 3) : origin u v w t + (u * v * w) * m ∈ values u v w t L i := by
      have hphys : physical u v w i ≤ w := by fin_cases i <;> norm_num [physical] <;> omega
      have hkm := (Nat.mul_le_mul_right m hphys).trans hwm
      have hk : physical u v w i * m < L := by omega
      have hval : scale u v w i * (centres u v w t i + physical u v w i * m) =
          origin u v w t + (u * v * w) * m := by
        rw [Nat.mul_add, common_product, ← Nat.mul_assoc, scale_physical]
      rw [← hval]
      exact internal_mem (by have hh := centres_ge_two hu huv hvw ht i; omega) hk
    exact mem_inter.mpr ⟨mem_inter.mpr ⟨hmem 0, hmem 1⟩, hmem 2⟩
  have hcard : J.card = (L - 1) / w + 1 := by
    dsimp only [J]
    rw [card_image_of_injective _ (fun _ _ hh ↦ Nat.eq_of_mul_eq_mul_left hM (Nat.add_left_cancel hh)), card_range]
  exact hcard.symm.trans_le (card_le_card hsub)

theorem triple_intersection_lower {u v w t L : ℕ} (hu : 2 ≤ u) (huv : u ≤ v) (hvw : v ≤ w)
    (ht : 1 ≤ t) (hL : 1 ≤ L) :
    ((L : ℝ) - 1) / w ≤
      (((values u v w t L 0 ∩ values u v w t L 1) ∩ values u v w t L 2).card : ℝ) := by
  have hw : 0 < w := by omega
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hrem := Nat.mod_lt (L - 1) hw
  have hdiv := Nat.div_add_mod (L - 1) w
  have hnat : L - 1 < w * ((L - 1) / w + 1) := by nlinarith only [hrem, hdiv]
  have hreal : (L : ℝ) - 1 < (w : ℝ) * (((L - 1) / w + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
  have hfloor : ((L : ℝ) - 1) / w ≤ (((L - 1) / w + 1 : ℕ) : ℝ) :=
    (div_le_iff₀ hwR).mpr (by nlinarith only [hreal])
  exact hfloor.trans (by exact_mod_cast triple_intersection_count hu huv hvw ht hL)

theorem union_loss_bound {u v w t L : ℕ} (hu : 2 ≤ u) (huv : u ≤ v) (hvw : v ≤ w)
    (ht : 1 ≤ t) (hL : 1 ≤ L) :
    3 * (L : ℝ) - (((valueUnion (scale u v w) (centres u v w t) L).card : ℝ) - 1) ≤
      RationalTripleDensity.density u v w * L + 5 := by
  let A := values u v w t L 0
  let B := values u v w t L 1
  let D := values u v w t L 2
  let U := valueUnion (scale u v w) (centres u v w t) L
  have hu0 : 0 < u := by omega
  have hv0 : 0 < v := by omega
  have hw0 : 0 < w := by omega
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv0
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw0
  have hlocal (i : Fin 3) : (values u v w t L i).card = L + 1 :=
    card_normalized (scale_pos hu0 hv0 hw0 i) (by have hh := centres_ge_two hu huv hvw ht i; omega)
  have hcard := ThreeUnionCard.identity A B D
  rw [← union_three u v w t L, hlocal 0, hlocal 1, hlocal 2] at hcard
  have hcardR : (U.card : ℝ) + (A ∩ B).card + (A ∩ D).card + (B ∩ D).card =
      3 * (L + 1) + (((A ∩ B) ∩ D).card : ℝ) := by
    have hh : U.card + (A ∩ B).card + (A ∩ D).card + (B ∩ D).card =
        3 * (L + 1) + ((A ∩ B) ∩ D).card := by dsimp only [U]; omega
    exact_mod_cast hh
  have hp01 := pair_zero_one_upper (L := L) hu0 hv0 hw0 ht
  have hp02 := pair_zero_two_upper (L := L) hu0 hv0 hw0 ht
  have hp12 := pair_one_two_upper (L := L) hu0 hv0 hw0 ht
  have hp012 := triple_intersection_lower hu huv hvw ht hL
  change ((A ∩ B).card : ℝ) ≤ _ at hp01
  change ((A ∩ D).card : ℝ) ≤ _ at hp02
  change ((B ∩ D).card : ℝ) ≤ _ at hp12
  change _ ≤ (((A ∩ B) ∩ D).card : ℝ) at hp012
  let d : ℝ := (Nat.gcd u v : ℝ) / v + (Nat.gcd u w : ℝ) / w + (Nat.gcd v w : ℝ) / w
  have hbound : 3 * (L : ℝ) - ((U.card : ℝ) - 1) ≤ (L + 1) * d - ((L : ℝ) - 1) / w + 1 := by
    dsimp only [d]
    push_cast at hp01 hp02 hp12
    simp only [div_eq_mul_inv] at hp01 hp02 hp12 hp012 ⊢
    nlinarith only [hcardR, hp01, hp02, hp12, hp012]
  have hd1 : (Nat.gcd u v : ℝ) / v ≤ 1 := (div_le_one hvR).mpr (by exact_mod_cast Nat.gcd_le_right u hv0)
  have hd2 : (Nat.gcd u w : ℝ) / w ≤ 1 := (div_le_one hwR).mpr (by exact_mod_cast Nat.gcd_le_right u hw0)
  have hd3 : (Nat.gcd v w : ℝ) / w ≤ 1 := (div_le_one hwR).mpr (by exact_mod_cast Nat.gcd_le_right v hw0)
  have hd : d ≤ 3 := by dsimp only [d]; linarith only [hd1, hd2, hd3]
  have hunit : 1 / (w : ℝ) ≤ 1 := (div_le_one hwR).mpr (by exact_mod_cast (show 1 ≤ w by omega))
  have hden : RationalTripleDensity.density u v w = d - 1 / (w : ℝ) := by
    rw [RationalTripleDensity.density_ordered huv hvw]
    dsimp only [d]
    ring
  have heq : (L + 1 : ℝ) * d - ((L : ℝ) - 1) / w + 1 =
      RationalTripleDensity.density u v w * L + d + 1 + 1 / (w : ℝ) := by rw [hden]; ring
  rw [heq] at hbound
  linarith only [hbound, hd, hunit]

theorem extremal_union_rank {u v w t L : ℕ} (huv : u < v) (hvw : v < w) (hw2u : w < 2 * u)
    (hprim : Nat.gcd (Nat.gcd u v) w = 1) (ht : 1 ≤ t) (hL : 1 ≤ L) :
    (71 / 30 : ℝ) * L - 5 ≤ (((valueUnion (scale u v w) (centres u v w t) L).card - 1 : ℕ) : ℝ) := by
  have hu : 2 ≤ u := by omega
  have hloss := union_loss_bound hu huv.le hvw.le ht hL
  have hd := RationalTripleOverlap.bound huv hvw hw2u hprim
  have hmul := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg L)
  have hcard : 1 ≤ (valueUnion (scale u v w) (centres u v w t) L).card := card_pos.mpr
    ⟨origin u v w t, normalized_subset _ _ _ 0 (common_mem hu huv.le hvw.le ht hL 0)⟩
  rw [Nat.cast_sub hcard, Nat.cast_one]
  linarith only [hloss, hmul]

theorem nonextremal_union_rank {u v w t L : ℕ} (huv : u < v) (hvw : v < w) (hw2u : w < 2 * u)
    (hprim : Nat.gcd (Nat.gcd u v) w = 1) (hne : ¬(u = 10 ∧ v = 12 ∧ w = 15))
    (ht : 1 ≤ t) (hL : 1 ≤ L) :
    (43 / 18 : ℝ) * L - 5 ≤ (((valueUnion (scale u v w) (centres u v w t) L).card - 1 : ℕ) : ℝ) := by
  have hu : 2 ≤ u := by omega
  have hloss := union_loss_bound hu huv.le hvw.le ht hL
  have hd := (RationalTripleOverlap.gap huv hvw hw2u hprim).resolve_left hne
  have hmul := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg L)
  have hcard : 1 ≤ (valueUnion (scale u v w) (centres u v w t) L).card := card_pos.mpr
    ⟨origin u v w t, normalized_subset _ _ _ 0 (common_mem hu huv.le hvw.le ht hL 0)⟩
  rw [Nat.cast_sub hcard, Nat.cast_one]
  linarith only [hloss, hmul]

end PaperP1.RationalTripleUnionRank
