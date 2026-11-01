module

public import PaperP1.Arithmetic.OffsetPlaneIntersections
public import PaperP1.Model.TripleProbabilityBound

/-! # The original affine joint mass on the intersection of two offset planes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetPlaneMass

open Finset PaperP1.OffsetPlaneIntersections PaperP1.TripleProbabilityBound
  PaperP1.Model.InfiniteStarts PaperP1.Arithmetic

def pairCenters (N L : ℕ) : Finset (Fin 3 → ℕ) := by
  classical
  exact (doubleCenters N L).filter (PairGood L)

def primitiveCenters (N L : ℕ) : Finset (Fin 3 → ℕ) := by
  classical
  exact (doubleCenters N L).filter fun X ↦ Function.Injective X ∧
    (∀ i, Module.finrank F₂ (squareClassSpace (X i) L) = L) ∧
    Pairwise (fun i j ↦ Disjoint (squareClassSpace (X i) L) (squareClassSpace (X j) L)) ∧ Primitive L X

def pairMass (N L : ℕ) : ℝ := ∑ X ∈ pairCenters N L, infiniteJointMoment L (tupleSet X)

def primitiveMass (N L : ℕ) : ℝ := ∑ X ∈ primitiveCenters N L, infiniteJointMoment L (tupleSet X)

theorem mem_pairCenters (N L : ℕ) (X : Fin 3 → ℕ) :
    X ∈ pairCenters N L ↔ X ∈ doubleCenters N L ∧ PairGood L X := by
  classical
  exact mem_filter

theorem mem_primitiveCenters (N L : ℕ) (X : Fin 3 → ℕ) :
    X ∈ primitiveCenters N L ↔ X ∈ doubleCenters N L ∧ Function.Injective X ∧
      (∀ i, Module.finrank F₂ (squareClassSpace (X i) L) = L) ∧
      Pairwise (fun i j ↦ Disjoint (squareClassSpace (X i) L) (squareClassSpace (X j) L)) ∧ Primitive L X := by
  classical
  exact mem_filter

theorem primitiveCenters_subset (N L : ℕ) : primitiveCenters N L ⊆ pairCenters N L := by
  intro X hX
  obtain ⟨hdouble, hinj, hrank, hpair, _⟩ := (mem_primitiveCenters N L X).mp hX
  exact (mem_pairCenters N L X).mpr ⟨hdouble, hinj.ne (by decide), hrank 0, hrank 1, hpair (by decide)⟩

theorem pairCenters_card_le (N L : ℕ) : (pairCenters N L).card ≤ (L + 1) ^ 18 * N := by
  classical
  exact (card_le_card (filter_subset _ _)).trans (doubleCenters_card_le N L)

theorem pairMass_nonneg (N L : ℕ) : 0 ≤ pairMass N L :=
  sum_nonneg fun X _ ↦ infiniteJointMoment_nonneg L (tupleSet X)

theorem primitiveMass_nonneg (N L : ℕ) : 0 ≤ primitiveMass N L :=
  sum_nonneg fun X _ ↦ infiniteJointMoment_nonneg L (tupleSet X)

theorem primitiveMass_le_pairMass (N L : ℕ) : primitiveMass N L ≤ pairMass N L := by
  exact sum_le_sum_of_subset_of_nonneg (primitiveCenters_subset N L)
    (fun X _ _ ↦ infiniteJointMoment_nonneg L (tupleSet X))

theorem pairMass_bound {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    pairMass N L ≤ ((L + 1 : ℕ) : ℝ) ^ 18 * N * ((2 ^ L : ℝ)⁻¹) ^ 2 := by
  classical
  calc
    _ ≤ ∑ _X ∈ pairCenters N L, ((2 ^ L : ℝ)⁻¹) ^ 2 := by
      apply sum_le_sum
      intro X hX
      obtain ⟨hdouble, hgood⟩ := (mem_pairCenters N L X).mp hX
      have hbox := ((mem_doubleCenters N L X).mp hdouble).1
      have hx := (mem_Ico.mp (hbox 0)).1
      have hy := (mem_Ico.mp (hbox 1)).1
      exact triple_joint_le X (by omega) (by omega) hL hgood
    _ = ((pairCenters N L).card : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ 2 := by simp
    _ ≤ (((L + 1 : ℕ) : ℝ) ^ 18 * N) * ((2 ^ L : ℝ)⁻¹) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast pairCenters_card_le N L

theorem primitiveMass_bound {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    primitiveMass N L ≤ ((L + 1 : ℕ) : ℝ) ^ 18 * N * ((2 ^ L : ℝ)⁻¹) ^ 2 :=
  (primitiveMass_le_pairMass N L).trans (pairMass_bound hN hL)

end PaperP1.OffsetPlaneMass
