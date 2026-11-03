module

public import PaperP1.Combinatorics.FamilyEnumerationWeights
public import PaperP1.Model.PrimitiveWindowMass
public import PaperP1.Model.RetainedDeficitGrouping

/-! # The literal ordered separated regular primitive lists and their nominal rank mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveOrderedMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies PaperP1.FiniteFamilyEnumeration

def lists (N L r : ℕ) : Finset (Fin r → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin r ↦ RegularStarts.regularStarts N L).filter fun n ↦
    Function.Injective n ∧ Primitive L (tupleSet n) ∧ ∀ i j, i ≠ j → L < Nat.dist (n i) (n j)

def mass (N L r : ℕ) : ℝ :=
  ∑ n ∈ lists N L r, ((2 ^ L : ℝ)⁻¹) ^ r * (2 ^ runRelativeNullity L (tupleSet n) : ℝ)

theorem mem_lists (N L r : ℕ) (n : Fin r → ℕ) : n ∈ lists N L r ↔
    (∀ i, n i ∈ RegularStarts.regularStarts N L) ∧ Function.Injective n ∧
      Primitive L (tupleSet n) ∧ ∀ i j, i ≠ j → L < Nat.dist (n i) (n j) := by
  classical
  simp only [lists, mem_filter, Fintype.mem_piFinset]

theorem tuple_regular {N L r : ℕ} {n : Fin r → ℕ} (hn : n ∈ lists N L r) :
    tupleSet n ⊆ RegularStarts.regularStarts N L := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := mem_image.mp hx
  exact ((mem_lists N L r n).mp hn).1 i

theorem weight_formula {N L r : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (n : Fin r → ℕ)
    (hn : n ∈ lists N L r) : PrimitiveWindowMass.weight L (tupleSet n) =
      ((2 ^ L : ℝ)⁻¹) ^ r * (2 ^ runRelativeNullity L (tupleSet n) : ℝ) := by
  rw [PrimitiveWindowMass.weight, RetainedDeficitGrouping.nominal_product hN hL _ (tuple_regular hn),
    FamilyEnumerationUpper.tupleSet_card n ((mem_lists N L r n).mp hn).2.1]
  rfl

theorem rank_formula {N L r : ℕ} {n : Fin r → ℕ} (hn : n ∈ lists N L r) :
    runRelativeNullity L (tupleSet n) = r * L - SubspaceFamilyRank.rank (fun x ↦ squareClassSpace x L) (tupleSet n) := by
  rw [RetainedGoodEdges.nullity_eq_rank_deficit N L _ (tuple_regular hn),
    FamilyEnumerationUpper.tupleSet_card n ((mem_lists N L r n).mp hn).2.1]

theorem finite_bound {N L r : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    mass N L r ≤ (r.factorial : ℝ) *
      PrimitiveWindowMass.mass (primitiveFamilies (RegularStarts.regularStarts N L) L r) L := by
  classical
  have hP : ∀ n ∈ lists N L r, Function.Injective n ∧
      tupleSet n ∈ primitiveFamilies (RegularStarts.regularStarts N L) L r := by
    intro n hn
    obtain ⟨_, hinj, hprim, _⟩ := (mem_lists N L r n).mp hn
    exact ⟨hinj, mem_filter.mpr ⟨mem_powersetCard.mpr
      ⟨tuple_regular hn, FamilyEnumerationUpper.tupleSet_card n hinj⟩, hprim⟩⟩
  calc
    _ = ∑ n ∈ lists N L r, PrimitiveWindowMass.weight L (tupleSet n) :=
      sum_congr rfl (fun n hn ↦ (weight_formula hN hL n hn).symm)
    _ ≤ _ := FamilyEnumerationWeights.weighted_bound _ _ (PrimitiveWindowMass.weight L)
      (PrimitiveWindowMass.weight_nonneg L) (fun I hI ↦ (mem_powersetCard.mp (mem_filter.mp hI).1).2) hP

end PaperP1.PrimitiveOrderedMass
