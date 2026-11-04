module

public import PaperP1.Diophantine.PrimitiveDirections
public import PaperP1.Algebra.RationalizedCriticalPointBound

/-! # Exact signed primitive multiplicity over an affine rational point -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveRationalPointLift

open Finset Polynomial PaperP1.PrimitiveDirections PaperP1.BivariateDegrees
  PaperP1.RationalBivariateIrreducibility

abbrev Point := Pair × Pair

def affine (s : Point) : ℚ × ℚ := (ratio s.1, ratio s.2)

theorem affine_fibre_card (S : Finset Point)
    (hprimitive : ∀ s ∈ S, (s.1 0).natAbs.Coprime (s.1 1).natAbs ∧
      (s.2 0).natAbs.Coprime (s.2 1).natAbs)
    (hden : ∀ s ∈ S, s.1 1 ≠ 0 ∧ s.2 1 ≠ 0) (r : ℚ × ℚ) :
    (S.filter fun s ↦ affine s = r).card ≤ 4 := by
  classical
  let T := S.filter fun s ↦ affine s = r
  change T.card ≤ 4
  by_cases hT : T.Nonempty
  · obtain ⟨v, hv⟩ := hT
    have hvS := (mem_filter.mp hv).1
    let A : Finset Pair := {v.1, negative v.1}
    let B : Finset Pair := {v.2, negative v.2}
    have hsub : T ⊆ A ×ˢ B := by
      intro s hs
      have hsS := (mem_filter.mp hs).1
      have heq : affine v = affine s :=
        (mem_filter.mp hv).2.trans (mem_filter.mp hs).2.symm
      have hfirst : ratio v.1 = ratio s.1 := congrArg Prod.fst heq
      have hsecond : ratio v.2 = ratio s.2 := congrArg Prod.snd heq
      have ha := primitive_same_direction v.1 s.1 (hprimitive v hvS).1
        (hprimitive s hsS).1 (equal_ratio_cross v.1 s.1 (hden v hvS).1 (hden s hsS).1 hfirst)
      have hb := primitive_same_direction v.2 s.2 (hprimitive v hvS).2
        (hprimitive s hsS).2 (equal_ratio_cross v.2 s.2 (hden v hvS).2 (hden s hsS).2 hsecond)
      exact mem_product.mpr ⟨by simpa only [A, mem_insert, mem_singleton] using ha,
        by simpa only [B, mem_insert, mem_singleton] using hb⟩
    have hA : A.card ≤ 2 := by
      exact (card_insert_le _ _).trans (by simp)
    have hB : B.card ≤ 2 := by
      exact (card_insert_le _ _).trans (by simp)
    exact (card_le_card hsub).trans (by
      rw [card_product]
      exact Nat.mul_le_mul hA hB)
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hT, card_empty, Nat.zero_le]

theorem card_le_four_image (S : Finset Point)
    (hprimitive : ∀ s ∈ S, (s.1 0).natAbs.Coprime (s.1 1).natAbs ∧
      (s.2 0).natAbs.Coprime (s.2 1).natAbs)
    (hden : ∀ s ∈ S, s.1 1 ≠ 0 ∧ s.2 1 ≠ 0) :
    S.card ≤ 4 * (S.image affine).card := by
  classical
  calc
    _ = ∑ r ∈ S.image affine, (S.filter fun s ↦ affine s = r).card :=
      card_eq_sum_card_image _ _
    _ ≤ ∑ _r ∈ S.image affine, 4 :=
      sum_le_sum (fun r _ ↦ affine_fibre_card S hprimitive hden r)
    _ = _ := by simp [Nat.mul_comm]

theorem primitive_critical_points_card (G : ℤ[X][X])
    (hG : Irreducible (rationalize G)) (hy : 0 < degreeY G) (S : Finset Point)
    (hprimitive : ∀ s ∈ S, (s.1 0).natAbs.Coprime (s.1 1).natAbs ∧
      (s.2 0).natAbs.Coprime (s.2 1).natAbs)
    (hden : ∀ s ∈ S, s.1 1 ≠ 0 ∧ s.2 1 ≠ 0)
    (hS : ∀ s ∈ S, (rationalize G).evalEval (ratio s.1) (ratio s.2) = 0 ∧
      (rationalize G).derivative.evalEval (ratio s.1) (ratio s.2) = 0) :
    S.card ≤ 8 * degreeX G * degreeY G ^ 2 := by
  classical
  have hc := PaperP1.RationalizedCriticalPointBound.critical_points_card
    G hG hy (S.image affine) (by
      intro p hp
      obtain ⟨s, hs, rfl⟩ := mem_image.mp hp
      exact hS s hs)
  calc
    _ ≤ 4 * (S.image affine).card := card_le_four_image S hprimitive hden
    _ ≤ 4 * (2 * degreeX G * degreeY G ^ 2) := Nat.mul_le_mul_left _ hc
    _ = _ := by ring

end PaperP1.PrimitiveRationalPointLift
