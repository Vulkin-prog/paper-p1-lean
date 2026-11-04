module

public import PaperP1.Arithmetic.SubsetEnvelopeGraph
public import PaperP1.Arithmetic.AsymmetricComponentOffsets

/-! # Free components of two prescribed subsets retain their actual physical roots -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SubsetComponentOffsets

open Finset PaperP1.Arithmetic PaperP1.AsymmetricEnvelopeGraph PaperP1.AsymmetricComponentOffsets
  PaperP1.LargePrimeGraph PaperP1.PinnedGraphResolution PaperP1.TwoBlockComponentSquares
  PaperP1.DefectivePredicate

theorem left_bound {x y H R : ℕ} (U V : Finset ℕ)
    (hU : ∀ n ∈ U, |(n : ℤ) - x| ≤ (R : ℤ))
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent)
    (hfree : ¬ComponentPinned _ (SubsetEnvelopeGraph.pins x y H R U V) c)
    (z : ℤ) (hz : z ∈ left x y H R c) : z.natAbs ≤ R := by
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
  have hcomp := (MediumPrimeColumns.mem_componentVertices _ c _).mp (mem_toLeft.mp hi)
  have hmem := SubsetEnvelopeGraph.old_mem_of_unpinned U V c hfree i hcomp
  have hh : |offset x H R i| ≤ (R : ℤ) := hU _ hmem
  rw [Int.abs_eq_natAbs] at hh
  exact_mod_cast hh

theorem right_bound {x y H R : ℕ} (U V : Finset ℕ)
    (hV : ∀ n ∈ V, |(n : ℤ) - y| ≤ (R : ℤ))
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent)
    (hfree : ¬ComponentPinned _ (SubsetEnvelopeGraph.pins x y H R U V) c)
    (z : ℤ) (hz : z ∈ right x y H R c) : z.natAbs ≤ R := by
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hz
  have hcomp := (MediumPrimeColumns.mem_componentVertices _ c _).mp (mem_toRight.mp hj)
  have hmem := SubsetEnvelopeGraph.new_mem_of_unpinned U V c hfree j hcomp
  have hh : |offset y H R j| ≤ (R : ℤ) := hV _ hmem
  rw [Int.abs_eq_natAbs] at hh
  exact_mod_cast hh

theorem coefficient_support {x y H R : ℕ} (hx : R < x) (hy : R < y) (U V : Finset ℕ)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent)
    (hfree : ¬ComponentPinned _ (SubsetEnvelopeGraph.pins x y H R U V) c) :
    oddPrimeSupport (product (start x R) (start y R) H c) ⊆ DefectCounting.smallPrimesUpTo (10 * (H + 1)) :=
  TwoBlockComponentSquares.support (start_ge_two hx) (start_ge_two hy) c
    (SubsetEnvelopeGraph.original_unpinned U V c hfree)

end PaperP1.SubsetComponentOffsets
