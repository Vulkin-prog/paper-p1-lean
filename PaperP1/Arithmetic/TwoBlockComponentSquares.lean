module

public import PaperP1.Arithmetic.MediumPrimeColumns
public import PaperP1.Arithmetic.RelativeSquarefreeParts

/-! # Actual unpinned two-window graph components give literal small-prime square prescriptions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoBlockComponentSquares

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.LargePrimeOccurrences
  PaperP1.LargePrimeGraph PaperP1.LargePrimeGraphResolution PaperP1.PinnedGraphResolution
  PaperP1.DefectivePredicate PaperP1.DefectCounting PaperP1.LargeOddKernel

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance (x y L : ℕ) : DecidableRel (largePrimeGraph x y L).Adj := Classical.decRel _

def vertices (x y L : ℕ) (c : (largePrimeGraph x y L).ConnectedComponent) : Finset (Occurrence L) :=
  MediumPrimeColumns.componentVertices (largePrimeGraph x y L) c

def product (x y L : ℕ) (c : (largePrimeGraph x y L).ConnectedComponent) : ℕ :=
  ∏ v ∈ vertices x y L c, twoStartCompleteVertexLabel x y L v

def indicator (x y L : ℕ) (c : (largePrimeGraph x y L).ConnectedComponent) (v : Occurrence L) : F₂ := by
  classical
  exact if (largePrimeGraph x y L).connectedComponentMk v = c then 1 else 0

theorem label_pos {x y L : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y) (v : Occurrence L) :
    0 < twoStartCompleteVertexLabel x y L v := by
  cases v with
  | inl i =>
    rw [twoStartCompleteVertexLabel, startCompleteVertexLabel_eq_offset (by omega : 0 < x)]
    omega
  | inr i =>
    rw [twoStartCompleteVertexLabel, startCompleteVertexLabel_eq_offset (by omega : 0 < y)]
    omega

theorem product_pos {x y L : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (c : (largePrimeGraph x y L).ConnectedComponent) : 0 < product x y L c :=
  prod_pos (fun v _ ↦ label_pos hx hy v)

theorem indicator_mem {x y L : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (c : (largePrimeGraph x y L).ConnectedComponent)
    (hfree : ¬ ComponentPinned (largePrimeGraph x y L) (pinnedVertices x y L) c) :
    indicator x y L c ∈ largePrimeSolution x y L := by
  classical
  rw [largePrimeSolution_eq_pinnedGraphSpace hx hy]
  constructor
  · intro v w hvw
    have heq := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hvw
    simp only [indicator, heq]
  · intro v hv
    have hne : (largePrimeGraph x y L).connectedComponentMk v ≠ c := fun h ↦ hfree ⟨v, hv, h⟩
    simp only [indicator, ite_eq_right hne]

theorem large_parity {x y L : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (c : (largePrimeGraph x y L).ConnectedComponent)
    (hfree : ¬ ComponentPinned (largePrimeGraph x y L) (pinnedVertices x y L) c)
    (p : ℕ) (hp : IsLargePrime L p) : parityVec (product x y L c) p = 0 := by
  classical
  have hsol := indicator_mem (by omega : 1 ≤ x) (by omega : 1 ≤ y) c hfree
  have hsum := mem_largePrimeSolution_iff_boundary_prime_equations.mp hsol p hp
  have hprod := congrArg (fun q : ℕ →₀ F₂ ↦ q p)
    (parityVec_prod (vertices x y L c) (twoStartCompleteVertexLabel x y L)
      (fun v _ ↦ (label_pos hx hy v).ne'))
  simp only [Finsupp.finsetSum_apply] at hprod
  change parityVec (product x y L c) p = _ at hprod
  have heq : (∑ v ∈ vertices x y L c, parityVec (twoStartCompleteVertexLabel x y L v) p) =
      ∑ v : Occurrence L, indicator x y L c v * parityVec (twoStartCompleteVertexLabel x y L v) p := by
    simp only [vertices, MediumPrimeColumns.componentVertices, sum_filter, indicator, ite_mul, one_mul, zero_mul]
  exact hprod.trans (heq.trans hsum)

theorem support {x y L : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (c : (largePrimeGraph x y L).ConnectedComponent)
    (hfree : ¬ ComponentPinned (largePrimeGraph x y L) (pinnedVertices x y L) c) :
    oddPrimeSupport (product x y L c) ⊆ smallPrimesUpTo (10 * (L + 1)) := by
  intro p hp
  have hprime := prime_of_mem_oddPrimeSupport hp
  apply mem_smallPrimesUpTo.mpr
  refine ⟨hprime, ?_⟩
  by_contra hlarge
  have hzero := large_parity hx hy c hfree p ⟨hprime, Nat.lt_of_not_ge hlarge⟩
  exact (mem_oddPrimeSupport_iff_parityVec_ne_zero.mp hp) hzero

theorem square_prescription {x y L : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (c : (largePrimeGraph x y L).ConnectedComponent) :
    IsSquare ((((oddPrimeSupport (product x y L c)).prod id : ℕ) : ℤ) * (product x y L c : ℤ)) := by
  have h := RelativeSquarefreeParts.kernel_mul_isSquare (product_pos hx hy c).ne'
  change IsSquare ((oddPrimeSupport (product x y L c)).prod id * product x y L c) at h
  exact_mod_cast h

end PaperP1.TwoBlockComponentSquares
