module

public import PaperP1.Arithmetic.SmoothSupportBounds
public import PaperP1.Arithmetic.LargeOddKernel
public import PaperP1.Diophantine.UniformQuadraticCount

@[expose] public section

/-!
# Finite witnesses for two-defect windows

Every positive start with two distinct defective offsets is covered by an
actual positive quadratic solution, together with its offsets and small-prime
supports. This is finite bookkeeping for the two-defect part of T1.3.
-/

namespace PaperP1.TwoDefectHosts

open Finset DefectCounting DefectivePredicate UniformQuadraticCount

abbrev Configuration := (ℕ × ℕ) × (Finset ℕ × Finset ℕ)

def configurations (H R : ℕ) : Finset Configuration :=
  (((range (R + 1)) ×ˢ (range (R + 1))).filter fun ij => ij.1 ≠ ij.2) ×ˢ
    ((smallPrimesUpTo H).powerset ×ˢ (smallPrimesUpTo H).powerset)

noncomputable def twoDefectStarts (H R X : ℕ) : Finset ℕ := by
  classical
  exact (Icc 1 X).filter fun x =>
    ∃ i ≤ R, ∃ j ≤ R, i ≠ j ∧ HDefective H (x + i) ∧ HDefective H (x + j)

theorem mem_twoDefectStarts {H R X x : ℕ} :
    x ∈ twoDefectStarts H R X ↔
      1 ≤ x ∧ x ≤ X ∧
        ∃ i ≤ R, ∃ j ≤ R, i ≠ j ∧ HDefective H (x + i) ∧ HDefective H (x + j) := by
  classical
  simp [twoDefectStarts, and_assoc]

noncomputable def quadraticSolutions (Y : ℕ) (w : Configuration) : Finset (ℤ × ℤ) :=
  positiveQuadraticSolutions (w.2.1.prod id) (w.2.2.prod id)
    ((w.1.1 : ℤ) - (w.1.2 : ℤ)) Y

noncomputable def candidateHostFamily (Y : ℕ) (w : Configuration) : Finset ℕ :=
  (quadraticSolutions Y w).image fun z => w.2.1.prod id * z.1.toNat ^ 2 - w.1.1

theorem mem_configurations {H R : ℕ} {w : Configuration} :
    w ∈ configurations H R ↔
      w.1.1 ≤ R ∧ w.1.2 ≤ R ∧ w.1.1 ≠ w.1.2 ∧
        w.2.1 ⊆ smallPrimesUpTo H ∧ w.2.2 ⊆ smallPrimesUpTo H := by
  simp [configurations, and_assoc]

theorem card_configurations_le (H R : ℕ) :
    (configurations H R).card ≤
      (R + 1) ^ 2 * ((smallPrimesUpTo H).powerset.card) ^ 2 := by
  have hoff :
      (((range (R + 1)) ×ˢ (range (R + 1))).filter fun ij => ij.1 ≠ ij.2).card ≤
        (R + 1) ^ 2 := by
    calc
      _ ≤ ((range (R + 1)) ×ˢ (range (R + 1))).card := card_filter_le _ _
      _ = (R + 1) ^ 2 := by simp [pow_two]
  simpa only [configurations, card_product, pow_two] using
    Nat.mul_le_mul_right
      ((smallPrimesUpTo H).powerset.card * (smallPrimesUpTo H).powerset.card) hoff

theorem representation_squarePart_pos {H n : ℕ}
    (rep : HDefectRepresentation H n) (hn : 0 < n) :
    0 < rep.squarePart := by
  by_contra h
  have hz : rep.squarePart = 0 := by omega
  have hnzero : n = 0 := by rw [rep.value_eq, hz]; simp
  omega

theorem representation_squarePart_le_height {H n Y : ℕ}
    (rep : HDefectRepresentation H n) (hnY : n ≤ Y) :
    rep.squarePart ≤ Y := by
  have hbound : rep.squarePart ≤ Nat.sqrt Y := by
    apply DefectCounting.squarePart_le_sqrt _ rep hnY
    intro p hp
    exact (mem_smallPrimesUpTo.mp hp).1.one_lt.le
  exact hbound.trans (Nat.sqrt_le_self Y)

theorem twoDefectStarts_subset_quadratic_union (H R X : ℕ) :
    twoDefectStarts H R X ⊆
      (configurations H R).biUnion (candidateHostFamily (X + R)) := by
  classical
  intro x hx
  obtain ⟨hx1, hxX, i, hi, j, hj, hij, hdi, hdj⟩ := mem_twoDefectStarts.mp hx
  let repS := representationOfHDefective hdi (by omega : x + i ≠ 0)
  let repT := representationOfHDefective hdj (by omega : x + j ≠ 0)
  have hrepS : x + i = repS.support.prod id * repS.squarePart ^ 2 := repS.value_eq
  have hrepT : x + j = repT.support.prod id * repT.squarePart ^ 2 := repT.value_eq
  let w : Configuration := ((i, j), (repS.support, repT.support))
  have hw : w ∈ configurations H R := by
    simp only [w, configurations, mem_product, mem_filter, mem_range, mem_powerset]
    exact ⟨⟨⟨by omega, by omega⟩, hij⟩, repS.support_subset, repT.support_subset⟩
  have hu := representation_squarePart_pos repS (by omega)
  have hv := representation_squarePart_pos repT (by omega)
  have huH := representation_squarePart_le_height repS (show x + i ≤ X + R by omega)
  have hvH := representation_squarePart_le_height repT (show x + j ≤ X + R by omega)
  let z : ℤ × ℤ := ((repS.squarePart : ℤ), (repT.squarePart : ℤ))
  have hz : z ∈ quadraticSolutions (X + R) w := by
    apply mem_positiveQuadraticSolutions.mpr
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · change ((repS.support.prod id : ℕ) : ℤ) * (repS.squarePart : ℤ) ^ 2 -
          ((repT.support.prod id : ℕ) : ℤ) * (repT.squarePart : ℤ) ^ 2 =
          (i : ℤ) - (j : ℤ)
      have hS : (x : ℤ) + i = ((repS.support.prod id : ℕ) : ℤ) * (repS.squarePart : ℤ) ^ 2 := by
        exact_mod_cast hrepS
      have hT : (x : ℤ) + j = ((repT.support.prod id : ℕ) : ℤ) * (repT.squarePart : ℤ) ^ 2 := by
        exact_mod_cast hrepT
      linarith
    · simpa only [z, Int.natAbs_natCast] using huH
    · simpa only [z, Int.natAbs_natCast] using hvH
    · change (0 : ℤ) < (repS.squarePart : ℤ)
      exact_mod_cast hu
    · change (0 : ℤ) < (repT.squarePart : ℤ)
      exact_mod_cast hv
  apply mem_biUnion.mpr
  refine ⟨w, hw, ?_⟩
  apply mem_image.mpr
  refine ⟨z, hz, ?_⟩
  change repS.support.prod id * ((repS.squarePart : ℤ).toNat) ^ 2 - i = x
  simp only [Int.toNat_natCast]
  omega

theorem card_twoDefectStarts_le_sum (H R X : ℕ) :
    (twoDefectStarts H R X).card ≤
      ∑ w ∈ configurations H R, (quadraticSolutions (X + R) w).card := by
  classical
  calc
    _ ≤ ((configurations H R).biUnion (candidateHostFamily (X + R))).card :=
      card_le_card (twoDefectStarts_subset_quadratic_union H R X)
    _ ≤ ∑ w ∈ configurations H R, (candidateHostFamily (X + R) w).card :=
      card_biUnion_le
    _ ≤ ∑ w ∈ configurations H R, (quadraticSolutions (X + R) w).card := by
      apply sum_le_sum
      intro w _
      exact card_image_le

/-- Finite aggregation of actual quadratic-solution bounds. The arithmetic
bound supplied here will be discharged uniformly by the proved T1.2 theorem. -/
theorem card_twoDefectStarts_le_box_bound
    {H R X : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hquad : ∀ w ∈ configurations H R,
      ((quadraticSolutions (X + R) w).card : ℝ) ≤ B) :
    ((twoDefectStarts H R X).card : ℝ) ≤
      (R + 1 : ℝ) ^ 2 * ((smallPrimesUpTo H).powerset.card : ℝ) ^ 2 * B := by
  have hcount : ((configurations H R).card : ℝ) ≤
      (R + 1 : ℝ) ^ 2 * ((smallPrimesUpTo H).powerset.card : ℝ) ^ 2 := by
    exact_mod_cast card_configurations_le H R
  calc
    _ ≤ ∑ w ∈ configurations H R, ((quadraticSolutions (X + R) w).card : ℝ) := by
      exact_mod_cast card_twoDefectStarts_le_sum H R X
    _ ≤ ∑ _w ∈ configurations H R, B := sum_le_sum hquad
    _ = ((configurations H R).card : ℝ) * B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount hB

end PaperP1.TwoDefectHosts

