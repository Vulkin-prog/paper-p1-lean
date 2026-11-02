module

public import PaperP1.Arithmetic.RationalDivisibilityFilters
public import PaperP1.Arithmetic.PhysicalNormalizedMatches
public import PaperP1.Arithmetic.AlignedTargetCanonicalRank

/-! # Two repeated physical slopes share only one complete-window endpoint and one divisibility class -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RepeatedCoefficientUnionRank

open Finset PaperP1.Arithmetic PaperP1.NormalizedWindowSets PaperP1.FiniteEvenSquareClasses
  PaperP1.IntervalDivisibilityCount PaperP1.ScaledTargetValues

theorem intersection_union_subset {p q x y z L : ℕ} (hpq : p.Coprime q) :
    (normalized q x L ∩ normalized p y L) ∪ (normalized q z L ∩ normalized p y L) ⊆
      dilate p (hits q y L) := by
  intro n hn
  rcases mem_union.mp hn with hn | hn
  · obtain ⟨m, hm, rfl⟩ := mem_image.mp (mem_inter.mp hn).2
    have hdiv := RationalDivisibilityFilters.normalized_dvd (mem_inter.mp hn).1
    exact mem_image.mpr ⟨m, mem_filter.mpr ⟨hm, hpq.symm.dvd_of_dvd_mul_left hdiv⟩, rfl⟩
  · obtain ⟨m, hm, rfl⟩ := mem_image.mp (mem_inter.mp hn).2
    have hdiv := RationalDivisibilityFilters.normalized_dvd (mem_inter.mp hn).1
    exact mem_image.mpr ⟨m, mem_filter.mpr ⟨hm, hpq.symm.dvd_of_dvd_mul_left hdiv⟩, rfl⟩

theorem union_rank {p q x y z L : ℕ} (hp : 0 < p) (hq : 2 ≤ q) (hpq : p.Coprime q)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z) (hoverlap : (values x L ∩ values z L).card ≤ 1) :
    (5 / 2 : ℝ) * L - 1 ≤
      ((((normalized q x L ∪ normalized p y L) ∪ normalized q z L).card - 1 : ℕ) : ℝ) := by
  have hqpos : 0 < q := by omega
  let A := normalized q x L
  let B := normalized p y L
  let D := normalized q z L
  let U := (A ∪ B) ∪ D
  have hA : A.card = L + 1 := card_normalized hqpos (by omega)
  have hB : B.card = L + 1 := card_normalized hp (by omega)
  have hD : D.card = L + 1 := card_normalized hqpos (by omega)
  have h₁ := card_union_add_card_inter A D
  have h₂ := card_union_add_card_inter (A ∪ D) B
  rw [union_inter_distrib_right] at h₂
  have hU : U = (A ∪ D) ∪ B := by dsimp only [U]; ac_rfl
  have hcard : U.card + (A ∩ D).card + ((A ∩ B) ∪ (D ∩ B)).card = 3 * (L + 1) := by rw [hU]; omega
  have hcardR : (U.card : ℝ) + (A ∩ D).card + ((A ∩ B) ∪ (D ∩ B)).card = 3 * (L + 1) := by exact_mod_cast hcard
  have hAC : ((A ∩ D).card : ℝ) ≤ 1 := by
    change ((normalized q x L ∩ normalized q z L).card : ℝ) ≤ 1
    rw [PhysicalNormalizedMatches.same_dilation_intersection hqpos]
    exact_mod_cast hoverlap
  have hsubset := card_le_card (intersection_union_subset (x := x) (y := y) (z := z) (L := L) hpq)
  have himage := @card_image_le ℕ ℕ (hits q y L) (fun n ↦ p * n) inferInstance
  have hcount := (count_bounds (L := L) hy hqpos).2
  have hmatches : (((A ∩ B) ∪ (D ∩ B)).card : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / q + 1 :=
    (by exact_mod_cast hsubset.trans himage : (((A ∩ B) ∪ (D ∩ B)).card : ℝ) ≤ (hits q y L).card).trans hcount
  have hdiv : ((L + 1 : ℕ) : ℝ) / q ≤ ((L + 1 : ℕ) : ℝ) / 2 :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) (by exact_mod_cast hq)
  have hUpos : 1 ≤ U.card := card_pos.mpr ((normalized_nonempty q x L).mono
    (subset_union_left.trans subset_union_left))
  change (5 / 2 : ℝ) * L - 1 ≤ ((U.card - 1 : ℕ) : ℝ)
  rw [Nat.cast_sub hUpos, Nat.cast_one]
  push_cast at hmatches hdiv
  linarith only [hcardR, hAC, hmatches, hdiv]

theorem physical_a_dilate (a b x y z L : ℕ) : allValues a b a 1 x y z L =
    dilate a ((normalized b x L ∪ normalized a y L) ∪ normalized b z L) := by
  rw [AlignedTargetCanonicalRank.allValues_eq_union, Nat.mul_one, dilate, image_union, image_union]
  change (normalized (b * a) x L ∪ normalized (a * a) y L) ∪ normalized (a * b) z L =
    (dilate a (normalized b x L) ∪ dilate a (normalized a y L)) ∪ dilate a (normalized b z L)
  rw [← ScaledNormalizedIntersections.normalized_scale, ← ScaledNormalizedIntersections.normalized_scale,
    ← ScaledNormalizedIntersections.normalized_scale, Nat.mul_comm b a]

theorem physical_b_dilate (a b x y z L : ℕ) : allValues a b b 1 x y z L =
    dilate b ((normalized b x L ∪ normalized a y L) ∪ normalized a z L) := by
  rw [AlignedTargetCanonicalRank.allValues_eq_union, Nat.mul_one, dilate, image_union, image_union]
  change (normalized (b * b) x L ∪ normalized (a * b) y L) ∪ normalized (a * b) z L =
    (dilate b (normalized b x L) ∪ dilate b (normalized a y L)) ∪ dilate b (normalized a z L)
  rw [← ScaledNormalizedIntersections.normalized_scale, ← ScaledNormalizedIntersections.normalized_scale,
    ← ScaledNormalizedIntersections.normalized_scale, Nat.mul_comm a b]

theorem physical_a_rank {a b x y z L : ℕ} (ha : 0 < a) (hb : 2 ≤ b) (hpq : a.Coprime b)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z) (hoverlap : (values x L ∩ values z L).card ≤ 1) :
    (5 / 2 : ℝ) * L - 1 ≤ (((allValues a b a 1 x y z L).card - 1 : ℕ) : ℝ) := by
  rw [physical_a_dilate, dilate, card_image_of_injective _ (mul_right_injective₀ ha.ne')]
  exact union_rank ha hb hpq hx hy hz hoverlap

theorem physical_b_rank {a b x y z L : ℕ} (ha : 2 ≤ a) (hb : 0 < b) (hpq : a.Coprime b)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z) (hoverlap : (values y L ∩ values z L).card ≤ 1) :
    (5 / 2 : ℝ) * L - 1 ≤ (((allValues a b b 1 x y z L).card - 1 : ℕ) : ℝ) := by
  rw [physical_b_dilate, dilate, card_image_of_injective _ (mul_right_injective₀ hb.ne')]
  have hh := union_rank hb ha hpq.symm hy hx hz hoverlap
  rwa [union_comm (normalized a y L) (normalized b x L)] at hh

theorem reduced_physical {a b c d : ℕ} (hcd : c.Coprime d) (hphys : c = a * d ∨ c = b * d) :
    d = 1 ∧ (c = a ∨ c = b) := by
  have hh := hcd.gcd_eq_one
  rcases hphys with hc | hc
  · rw [hc, Nat.gcd_mul_left_left] at hh
    exact ⟨hh, Or.inl (by simpa only [hh, Nat.mul_one] using hc)⟩
  · rw [hc, Nat.gcd_mul_left_left] at hh
    exact ⟨hh, Or.inr (by simpa only [hh, Nat.mul_one] using hc)⟩

theorem triple_distinct {x y z : ℕ} (hcard : ({x, y, z} : Finset ℕ).card = 3) : x ≠ z ∧ y ≠ z := by
  have hpair (a b : ℕ) : ({a, b} : Finset ℕ).card ≤ 2 := by
    have hh := card_insert_le a ({b} : Finset ℕ)
    simpa only [card_singleton] using hh
  constructor
  · intro hh
    have hsmall := (card_le_card (by simp [hh] : ({x, y, z} : Finset ℕ) ⊆ {y, z})).trans (hpair y z)
    omega
  · intro hh
    have hsmall := (card_le_card (by simp [hh] : ({x, y, z} : Finset ℕ) ⊆ {x, z})).trans (hpair x z)
    omega

end PaperP1.RepeatedCoefficientUnionRank
