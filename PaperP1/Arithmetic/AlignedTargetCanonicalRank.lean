module

public import PaperP1.Arithmetic.AffineRationalTripleUnionRank
public import PaperP1.Arithmetic.ScaledTargetValues
public import PaperP1.Model.NormalizedFamilyDilation

/-! # The distinct physical slopes of any aligned target inherit the uniform canonical rank bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AlignedTargetCanonicalRank

open Finset PaperP1.Arithmetic PaperP1.NormalizedWindowSets PaperP1.FiniteEvenSquareClasses
  PaperP1.PrivateNormalizedFamilies PaperP1.RationalTripleNormalizers PaperP1.ScaledTargetValues

theorem allValues_eq_union (a b c d x y z L : ℕ) :
    allValues a b c d x y z L =
      (normalized (b * c) x L ∪ normalized (a * c) y L) ∪ normalized (a * b * d) z L := by
  rw [allValues, oldValues, newValues, NormalizedWindowSets.union, dilate, image_union]
  change (dilate c (normalized b x L) ∪ dilate c (normalized a y L)) ∪ normalized (a * b * d) z L = _
  rw [← ScaledNormalizedIntersections.normalized_scale, ← ScaledNormalizedIntersections.normalized_scale,
    Nat.mul_comm c b, Nat.mul_comm c a]

theorem allValues_eq_family (a b c d x y z L : ℕ) :
    valueUnion ![b * c, a * c, a * b * d] ![x, y, z] L = allValues a b c d x y z L := by
  have hu : (univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  rw [valueUnion, hu]
  simp only [biUnion_insert, singleton_biUnion]
  rw [allValues_eq_union]
  change normalized (b * c) x L ∪ (normalized (a * c) y L ∪ normalized (a * b * d) z L) =
    (normalized (b * c) x L ∪ normalized (a * c) y L) ∪ normalized (a * b * d) z L
  exact (union_assoc _ _ _).symm

theorem product_union_dilate (a b c d x y z L : ℕ) :
    valueUnion (scale (a * d) (b * d) c) ![x, y, z] L = dilate d (allValues a b c d x y z L) := by
  have hs : scale (a * d) (b * d) c = (fun i ↦ d * (![b * c, a * c, a * b * d] : Fin 3 → ℕ) i) := by
    funext i
    fin_cases i <;> norm_num [scale] <;> ring
  rw [hs, NormalizedFamilyDilation.union_dilate, allValues_eq_family]

theorem product_union_dilate_middle (a b c d x y z L : ℕ) :
    valueUnion (scale (a * d) c (b * d)) ![x, z, y] L = dilate d (allValues a b c d x y z L) := by
  rw [← product_union_dilate a b c d x y z L, AffineRationalTripleUnionRank.union_three,
    AffineRationalTripleUnionRank.union_three]
  change (normalized (c * (b * d)) x L ∪ normalized ((a * d) * (b * d)) z L) ∪ normalized ((a * d) * c) y L =
    (normalized ((b * d) * c) x L ∪ normalized ((a * d) * c) y L) ∪ normalized ((a * d) * (b * d)) z L
  ac_rfl

theorem product_union_dilate_left (a b c d x y z L : ℕ) :
    valueUnion (scale c (a * d) (b * d)) ![z, x, y] L = dilate d (allValues a b c d x y z L) := by
  rw [← product_union_dilate a b c d x y z L, AffineRationalTripleUnionRank.union_three,
    AffineRationalTripleUnionRank.union_three]
  change (normalized ((a * d) * (b * d)) z L ∪ normalized (c * (b * d)) x L) ∪ normalized (c * (a * d)) y L =
    (normalized ((b * d) * c) x L ∪ normalized ((a * d) * c) y L) ∪ normalized ((a * d) * (b * d)) z L
  ac_rfl

theorem physical_primitive {a b c d : ℕ} (hab : a.Coprime b) (hcd : c.Coprime d) :
    Nat.gcd (Nat.gcd (a * d) (b * d)) c = 1 := by
  rw [Nat.gcd_mul_right, hab.gcd_eq_one, one_mul, hcd.symm.gcd_eq_one]

theorem canonical_rank {a b c d x y z L : ℕ} (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (hd : 0 < d) (hcd : c.Coprime d)
    (hTop : c < 2 * (a * d)) (hLow : b * d < 2 * c) (hca : c ≠ a * d) (hcb : c ≠ b * d)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z) :
    (71 / 30 : ℝ) * L - 3 ≤ (((allValues a b c d x y z L).card - 1 : ℕ) : ℝ) := by
  have habd : a * d < b * d := Nat.mul_lt_mul_of_pos_right hab hd
  have hb2ad : b * d < 2 * (a * d) := by nlinarith only [Nat.mul_lt_mul_of_pos_right hb2a hd]
  have hprim := physical_primitive hcop hcd
  rcases lt_trichotomy c (a * d) with hleft | heq | hright
  · have hprim' : Nat.gcd (Nat.gcd c (a * d)) (b * d) = 1 := by
      rw [← hprim]
      ac_rfl
    have hXX : ∀ i, 2 ≤ (![z, x, y] : Fin 3 → ℕ) i := by intro i; fin_cases i <;> assumption
    have hh := AffineRationalTripleUnionRank.extremal_union_rank (L := L) hleft habd hLow hprim' ![z, x, y] hXX
    rw [product_union_dilate_left, dilate, card_image_of_injective _ (mul_right_injective₀ hd.ne')] at hh
    exact hh
  · exact False.elim (hca heq)
  · rcases lt_trichotomy c (b * d) with hmiddle | heq | hlast
    · have hprim' : Nat.gcd (Nat.gcd (a * d) c) (b * d) = 1 := by
        rw [← hprim]
        ac_rfl
      have hXX : ∀ i, 2 ≤ (![x, z, y] : Fin 3 → ℕ) i := by intro i; fin_cases i <;> assumption
      have hh := AffineRationalTripleUnionRank.extremal_union_rank (L := L) hright hmiddle hb2ad hprim' ![x, z, y] hXX
      rw [product_union_dilate_middle, dilate, card_image_of_injective _ (mul_right_injective₀ hd.ne')] at hh
      exact hh
    · exact False.elim (hcb heq)
    · have hXX : ∀ i, 2 ≤ (![x, y, z] : Fin 3 → ℕ) i := by intro i; fin_cases i <;> assumption
      have hh := AffineRationalTripleUnionRank.extremal_union_rank (L := L) habd hlast hTop hprim ![x, y, z] hXX
      rw [product_union_dilate, dilate, card_image_of_injective _ (mul_right_injective₀ hd.ne')] at hh
      exact hh

end PaperP1.AlignedTargetCanonicalRank
