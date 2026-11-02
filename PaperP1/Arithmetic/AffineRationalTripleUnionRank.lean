module

public import PaperP1.Arithmetic.RationalDivisibilityFilters
public import PaperP1.Arithmetic.RationalTripleOverlap

/-! # A finite canonical-overlap bound for arbitrary affine positions, with absolute error three -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AffineRationalTripleUnionRank

open Finset PaperP1.Arithmetic PaperP1.NormalizedWindowSets PaperP1.PrivateNormalizedFamilies
  PaperP1.RationalTripleNormalizers

theorem union_three (u v w L : ℕ) (X : Fin 3 → ℕ) :
    valueUnion (scale u v w) X L =
      (normalized (v * w) (X 0) L ∪ normalized (u * w) (X 1) L) ∪ normalized (u * v) (X 2) L := by
  have hu : (univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  rw [valueUnion, hu]
  simp only [biUnion_insert, singleton_biUnion]
  exact union_assoc _ _ _ |>.symm

theorem union_loss_bound {u v w L : ℕ} (huv : u < v) (hvw : v < w) (hw2u : w < 2 * u)
    (hprim : Nat.gcd (Nat.gcd u v) w = 1) (X : Fin 3 → ℕ) (hX : ∀ i, 2 ≤ X i) :
    3 * (L : ℝ) - (((valueUnion (scale u v w) X L).card : ℝ) - 1) ≤
      RationalTripleDensity.density u v w * L + 3 := by
  have hu : 0 < u := by omega
  have hv : 0 < v := by omega
  have hw : 0 < w := by omega
  let A := normalized (v * w) (X 0) L
  let B := normalized (u * w) (X 1) L
  let D := normalized (u * v) (X 2) L
  let U := valueUnion (scale u v w) X L
  have hA : A.card = L + 1 := card_normalized (Nat.mul_pos hv hw) (by have hh := hX 0; omega)
  have hB : B.card = L + 1 := card_normalized (Nat.mul_pos hu hw) (by have hh := hX 1; omega)
  have hD : D.card = L + 1 := card_normalized (Nat.mul_pos hu hv) (by have hh := hX 2; omega)
  have h₁ := card_union_add_card_inter A B
  have h₂ := card_union_add_card_inter (A ∪ B) D
  rw [union_inter_distrib_right] at h₂
  have hU : U = (A ∪ B) ∪ D := union_three u v w L X
  have hcard : U.card + (A ∩ B).card + ((A ∩ D) ∪ (B ∩ D)).card = 3 * (L + 1) := by
    rw [hU]
    omega
  have hcardR : (U.card : ℝ) + (A ∩ B).card + ((A ∩ D) ∪ (B ∩ D)).card = 3 * (L + 1) := by
    exact_mod_cast hcard
  have hp := ScaledNormalizedIntersections.reduced_intersection_bound (c := w) (u := u) (v := v)
    (x := X 0) (y := X 1) (L := L) hw hu hv (by have hh := hX 0; omega) (by have hh := hX 1; omega)
  rw [Nat.mul_comm w v, Nat.mul_comm w u] at hp
  change ((A ∩ B).card : ℝ) ≤ _ at hp
  have ht := RationalDivisibilityFilters.intersection_union_bound (x := X 0) (y := X 1) (L := L)
    hu hv hw (hX 2) hprim
  change (((A ∩ D) ∪ (B ∩ D)).card : ℝ) ≤ _ at ht
  have hbase : 3 * (L : ℝ) - ((U.card : ℝ) - 1) ≤
      RationalTripleDensity.density u v w * ((L + 1 : ℕ) : ℝ) + 2 := by
    rw [RationalTripleDensity.density_ordered huv.le hvw.le]
    push_cast at hp ht ⊢
    simp only [div_eq_mul_inv] at hp ht ⊢
    nlinarith only [hcardR, hp, ht]
  have hden := RationalTripleOverlap.bound huv hvw hw2u hprim
  push_cast at hbase
  nlinarith only [hbase, hden]

theorem extremal_union_rank {u v w L : ℕ} (huv : u < v) (hvw : v < w) (hw2u : w < 2 * u)
    (hprim : Nat.gcd (Nat.gcd u v) w = 1) (X : Fin 3 → ℕ) (hX : ∀ i, 2 ≤ X i) :
    (71 / 30 : ℝ) * L - 3 ≤ (((valueUnion (scale u v w) X L).card - 1 : ℕ) : ℝ) := by
  have hloss := union_loss_bound (L := L) huv hvw hw2u hprim X hX
  have hd := mul_le_mul_of_nonneg_right (RationalTripleOverlap.bound huv hvw hw2u hprim) (Nat.cast_nonneg L)
  have hcard : 1 ≤ (valueUnion (scale u v w) X L).card := by
    apply card_pos.mpr
    exact (normalized_nonempty (scale u v w 0) (X 0) L).mono (normalized_subset _ _ _ 0)
  rw [Nat.cast_sub hcard, Nat.cast_one]
  linarith only [hloss, hd]

theorem nonextremal_union_rank {u v w L : ℕ} (huv : u < v) (hvw : v < w) (hw2u : w < 2 * u)
    (hprim : Nat.gcd (Nat.gcd u v) w = 1) (hne : ¬(u = 10 ∧ v = 12 ∧ w = 15))
    (X : Fin 3 → ℕ) (hX : ∀ i, 2 ≤ X i) :
    (43 / 18 : ℝ) * L - 3 ≤ (((valueUnion (scale u v w) X L).card - 1 : ℕ) : ℝ) := by
  have hloss := union_loss_bound (L := L) huv hvw hw2u hprim X hX
  have hden := (RationalTripleOverlap.gap huv hvw hw2u hprim).resolve_left hne
  have hd := mul_le_mul_of_nonneg_right hden (Nat.cast_nonneg L)
  have hcard : 1 ≤ (valueUnion (scale u v w) X L).card := by
    apply card_pos.mpr
    exact (normalized_nonempty (scale u v w 0) (X 0) L).mono (normalized_subset _ _ _ 0)
  rw [Nat.cast_sub hcard, Nat.cast_one]
  linarith only [hloss, hd]

end PaperP1.AffineRationalTripleUnionRank
