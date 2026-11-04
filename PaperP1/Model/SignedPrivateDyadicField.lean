module

public import PaperP1.Model.SignedPrivateField
public import PaperP1.Arithmetic.PrivateDirectedFootprint

/-! # Literal retained dyadic starts for the specified signed forcing

The paper uses a run start `x`; the forcing word begins at `x-1`.
Every excess up to `E` is retained at every admitted start. The entire
maximal support has pivots above `Y=2*(L+E+2)`.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedPrivateDyadicField

open Finset PaperP1.Model PaperP1.OddPrimePivot PaperP1.SignedPrivateField

local instance signedPrivateDyadicFieldDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

def pivotCutoff (L E : ℕ) : ℕ := 2 * (L + E + 2)

def cylinderCutoff (N L E : ℕ) : ℕ := 2 * N + (L + E + 2)

def retainedStarts (N L E : ℕ) : Finset ℕ :=
  (dyadicBlock N).filter fun x ↦ ∀ i : Fin (L + E + 2),
    pivotCutoff L E < largestOddPrime (x - 1 + i.val)

def retainedBoundaries (N L E : ℕ) : Finset ℕ :=
  (retainedStarts N L E).image (fun x ↦ x - 1)

theorem boundary_recover {N L E j : ℕ} (hN : 2 ≤ N)
    (hj : j ∈ retainedBoundaries N L E) : j + 1 ∈ retainedStarts N L E := by
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hj
  have hxN := (mem_Ico.mp (mem_filter.mp hx).1).1
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ x)] using hx

theorem retained_start_iff {N L E x : ℕ} (hN : 2 ≤ N) :
    x ∈ retainedStarts N L E ↔ x - 1 ∈ retainedBoundaries N L E ∧ N ≤ x := by
  constructor
  · intro hx
    exact ⟨mem_image.mpr ⟨x, hx, rfl⟩, (mem_Ico.mp (mem_filter.mp hx).1).1⟩
  · rintro ⟨hx, hxN⟩
    have h := boundary_recover hN hx
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ x)] using h

theorem boundaries_card (N L E : ℕ) : (retainedBoundaries N L E).card ≤ N := by
  calc
    _ ≤ (retainedStarts N L E).card := card_image_le
    _ ≤ (dyadicBlock N).card := card_filter_le _ _
    _ = N := by simp [dyadicBlock, two_mul]

theorem boundary_vertices {N L E j : ℕ} (hN : 2 ≤ N)
    (hB : L + E + 2 ≤ N) (hj : j ∈ retainedBoundaries N L E)
    (i : Fin (L + E + 2)) : j + i.val ∈ Icc 1 (3 * N) := by
  have hx := boundary_recover hN hj
  have hdyadic := mem_Ico.mp (mem_filter.mp hx).1
  have hi := i.isLt
  exact mem_Icc.mpr ⟨by omega, by omega⟩

theorem data {N L E : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L) :
    Data (cylinderCutoff N L E) (pivotCutoff L E) L E (retainedBoundaries N L E) := {
  length_pos := hL
  boundary_pos := by
    intro j hj
    have hx := boundary_recover hN hj
    have h := (mem_Ico.mp (mem_filter.mp hx).1).1
    omega
  cutoff := by
    intro j hj
    have hx := boundary_recover hN hj
    have h := (mem_Ico.mp (mem_filter.mp hx).1).2
    dsimp [cylinderCutoff]
    omega
  small_cutoff := by dsimp [pivotCutoff]; omega
  good := by
    intro j hj i
    have h := (mem_filter.mp (boundary_recover hN hj)).2 i
    simpa only [Nat.add_sub_cancel] using h
  }

theorem actual_source_marginal {N L E : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L)
    (a : Index (retainedBoundaries N L E) E) :
    PaperP1.Probability.exactMarginal (cylinderProbability (cylinderCutoff N L E))
      (indicator (cylinderCutoff N L E) L) a =
        PaperP1.SignedExactWords.signedMarkRate L a.2.1.val :=
  indicator_marginal (data hN hL) a

theorem total_marginal_bound {N L E : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L) :
    (∑ a : Index (retainedBoundaries N L E) E,
      PaperP1.Probability.exactMarginal (cylinderProbability (cylinderCutoff N L E))
        (indicator (cylinderCutoff N L E) L) a) ≤ (N : ℝ) * (2 ^ L : ℝ)⁻¹ := by
  calc
    _ ≤ ((retainedBoundaries N L E).card : ℝ) * (2 ^ L : ℝ)⁻¹ := total_marginal_le (data hN hL)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast boundaries_card N L E) (by positivity)

end PaperP1.SignedPrivateDyadicField
