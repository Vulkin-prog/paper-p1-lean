module

public import PaperP1.Arithmetic.ThreeBlockRigidity
public import PaperP1.Arithmetic.SharedPrimeCover
public import PaperP1.Arithmetic.CoverRankPrimeBudget
public import PaperP1.Model.RegularStarts

/-! # Companion T20.7 on the actual covered three-window relation space -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TripleCoverRank

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.RegularStarts
  PaperP1.ThreeBlockCoordinates PaperP1.ThreeBlockRigidity PaperP1.CoverGraphResolution
  PaperP1.ColoredPrimeConstraints PaperP1.PinnedGraphResolution PaperP1.ThreeBlockComponents
  PaperP1.LocalDefectBound PaperP1.LargeOddKernel PaperP1.DefectivePredicate

local instance tripleCoverRankTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance tripleCoverComponentDecidableEq (X : Fin 3 → ℕ) (L H : ℕ) (D : Finset (Vertex L)) :
    DecidableEq (graph (rows X L H) D).ConnectedComponent := Classical.decEq _

def fullCount (X : Fin 3 → ℕ) (L H : ℕ) (D : Finset (Vertex L)) : ℕ :=
  (fullComponents (graph (rows X L H) D) (pins (rows X L H) D) Prod.fst).card

def componentVertices (X : Fin 3 → ℕ) (L H : ℕ) (D : Finset (Vertex L))
    (c : (graph (rows X L H) D).ConnectedComponent) : Finset (Vertex L) :=
  univ.filter (fun v ↦ (graph (rows X L H) D).connectedComponentMk v = c)

def componentProduct (X : Fin 3 → ℕ) (L H : ℕ) (D : Finset (Vertex L))
    (c : (graph (rows X L H) D).ConnectedComponent) : ℕ :=
  ∏ v ∈ componentVertices X L H D c, label X L v

theorem label_pos {X : Fin 3 → ℕ} {L : ℕ} (hX : ∀ i, 2 ≤ X i) (v : Vertex L) : 0 < label X L v := by
  rw [label, startCompleteVertexLabel_eq_offset (show 0 < X v.1 by have h := hX v.1; omega)]
  have h := hX v.1
  omega

theorem component_product_pos {X : Fin 3 → ℕ} {L H : ℕ} (hX : ∀ i, 2 ≤ X i)
    (D : Finset (Vertex L)) (c : (graph (rows X L H) D).ConnectedComponent) :
    0 < componentProduct X L H D c := prod_pos (fun v _ ↦ label_pos hX v)

def SquareModulo (H n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ DefectCounting.smallPrimesUpTo H ∧ ∃ a : ℕ, n = S.prod id * a ^ 2

theorem component_product_large_parity {X : Fin 3 → ℕ} {L H : ℕ} (hX : ∀ i, 2 ≤ X i)
    (hH : L + 1 ≤ H) {D : Finset (Vertex L)} (hD : IsCover (rows X L H) D)
    (c : (graph (rows X L H) D).ConnectedComponent)
    (hfree : ¬ComponentPinned (graph (rows X L H) D) (pins (rows X L H) D) c)
    (p : LargePrime H) : parityVec (componentProduct X L H D c) p.val = 0 := by
  have hsum := free_component_prime_sum (data X L) H (rows X L H)
    (rows_card_le_three (fun i ↦ (by have h := hX i; omega)) hH) (row_equation X L H) hD c hfree p
  have hnonzero : ∀ v ∈ componentVertices X L H D c, label X L v ≠ 0 := by
    intro v _
    rw [label, startCompleteVertexLabel_eq_offset (show 0 < X v.1 by have h := hX v.1; omega)]
    have h := hX v.1
    omega
  have hprod := congrArg (fun q : ℕ →₀ F₂ ↦ q p.val)
    (parityVec_prod (componentVertices X L H D c) (label X L) hnonzero)
  simp only [Finsupp.finsetSum_apply] at hprod
  change parityVec (componentProduct X L H D c) p.val = _ at hprod
  exact hprod.trans hsum

theorem component_product_supported {X : Fin 3 → ℕ} {L H : ℕ} (hX : ∀ i, 2 ≤ X i)
    (hH : L + 1 ≤ H) {D : Finset (Vertex L)} (hD : IsCover (rows X L H) D)
    (c : (graph (rows X L H) D).ConnectedComponent)
    (hfree : ¬ComponentPinned (graph (rows X L H) D) (pins (rows X L H) D) c) :
    oddPrimeSupport (componentProduct X L H D c) ⊆ DefectCounting.smallPrimesUpTo H := by
  intro p hp
  have hpprime := prime_of_mem_oddPrimeSupport hp
  apply DefectCounting.mem_smallPrimesUpTo.mpr
  refine ⟨hpprime, ?_⟩
  by_contra hlarge
  have hzero := component_product_large_parity hX hH hD c hfree ⟨p, hpprime, Nat.lt_of_not_ge hlarge⟩
  exact (mem_oddPrimeSupport_iff_parityVec_ne_zero.mp hp) hzero

theorem component_product_square_small {X : Fin 3 → ℕ} {L H : ℕ} (hX : ∀ i, 2 ≤ X i)
    (hH : L + 1 ≤ H) {D : Finset (Vertex L)} (hD : IsCover (rows X L H) D)
    (c : (graph (rows X L H) D).ConnectedComponent)
    (hfree : ¬ComponentPinned (graph (rows X L H) D) (pins (rows X L H) D) c) :
    SquareModulo H (componentProduct X L H D c) := by
  exact ⟨oddPrimeSupport (componentProduct X L H D c), component_product_supported hX hH hD c hfree,
    canonicalSquarePart (componentProduct X L H D c),
    canonical_odd_mul_sq_decomposition (component_product_pos hX D c).ne'⟩

theorem finite_rank_bound {X : Fin 3 → ℕ} {L H : ℕ} (hX : ∀ i, 2 ≤ X i) (hH : L + 1 ≤ H)
    (hinj : ∀ i, Function.Injective (evenSquareClassMap (X i) L))
    (hpair : Pairwise (fun i j ↦ Disjoint (squareClassSpace (X i) L) (squareClassSpace (X j) L)))
    (D : Finset (Vertex L)) (hD : IsCover (rows X L H) D) :
    Module.finrank F₂ (relativeSpace X L) ≤ D.card +
      Module.finrank F₂ (CoordinateRestrictionRank.zeroed (relativeSpace X L) D) ∧
    Module.finrank F₂ (CoordinateRestrictionRank.zeroed (relativeSpace X L) D) ≤
      fullCount X L H D + 3 * (primeCount H + 2) := by
  refine ⟨CoordinateRestrictionRank.cover_cost _ _, ?_⟩
  exact ThreeBlockComponents.residual_rank_bound Prod.fst (data X L) H (rows X L H)
    (rows_card_le_three (fun i ↦ (by have h := hX i; omega)) hH) (row_equation X L H)
    (nonprime_data X L) (pairwise_rigid X L hinj hpair) hD (relativeSpace X L) (relativeSpace_le_rows X L H)

def cutoff (C₀ : ℝ) (L : ℕ) : ℕ := ⌊C₀ * ((L + 1 : ℕ) : ℝ)⌋₊

theorem cutoff_bounds {C₀ : ℝ} (hC₀ : 1 ≤ C₀) (L : ℕ) :
    L + 1 ≤ cutoff C₀ L ∧ (cutoff C₀ L : ℝ) ≤ C₀ * ((L + 1 : ℕ) : ℝ) := by
  have hB : (0 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  constructor
  · apply Nat.le_floor
    nlinarith
  · exact Nat.floor_le (mul_nonneg (by linarith) hB)

theorem prime_above_cutoff {C₀ : ℝ} (hC₀ : 1 ≤ C₀) (L p : ℕ) :
    cutoff C₀ L < p ↔ C₀ * ((L + 1 : ℕ) : ℝ) < (p : ℝ) :=
  Nat.floor_lt (mul_nonneg (by linarith) (Nat.cast_nonneg _))

theorem smallPrime_at_cutoff {C₀ : ℝ} (hC₀ : 1 ≤ C₀) (L p : ℕ) :
    p ∈ DefectCounting.smallPrimesUpTo (cutoff C₀ L) ↔
      p.Prime ∧ (p : ℝ) ≤ C₀ * ((L + 1 : ℕ) : ℝ) := by
  rw [DefectCounting.mem_smallPrimesUpTo]
  constructor
  · rintro ⟨hp, hpH⟩
    exact ⟨hp, (show (p : ℝ) ≤ cutoff C₀ L by exact_mod_cast hpH).trans (cutoff_bounds hC₀ L).2⟩
  · rintro ⟨hp, hpH⟩
    exact ⟨hp, Nat.le_floor hpH⟩

/-- All source conclusions, uniform in every cover; no defective-vertex estimate is assumed. -/
theorem companion_T20_7 (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ C : ℝ, ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ X : Fin 3 → ℕ,
      (∀ i, X i ∈ regularStarts N L) →
      Pairwise (fun i j ↦ Disjoint (squareClassSpace (X i) L) (squareClassSpace (X j) L)) →
      ∀ D : Finset (Vertex L), SharedPrimeCover.CoversShared X L (cutoff C₀ L) D →
        Module.finrank F₂ (relativeSpace X L) ≤ D.card +
          Module.finrank F₂ (CoordinateRestrictionRank.zeroed (relativeSpace X L) D) ∧
        (Module.finrank F₂ (CoordinateRestrictionRank.zeroed (relativeSpace X L) D) : ℝ) ≤
          fullCount X L (cutoff C₀ L) D + K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) ∧
        ∀ c : (graph (rows X L (cutoff C₀ L)) D).ConnectedComponent,
          ¬ComponentPinned (graph (rows X L (cutoff C₀ L)) D) (pins (rows X L (cutoff C₀ L)) D) c →
          oddPrimeSupport (componentProduct X L (cutoff C₀ L) D c) ⊆ DefectCounting.smallPrimesUpTo (cutoff C₀ L) ∧
            SquareModulo (cutoff C₀ L) (componentProduct X L (cutoff C₀ L) D c) := by
  refine ⟨CoverRankPrimeBudget.constant C₀, CoverRankPrimeBudget.constant_pos hC₀, fun C ↦ ?_⟩
  obtain ⟨N₀, hN₀, hlarge⟩ := CoverRankPrimeBudget.critical_width_at_least_four C
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband X hreg hpair D hcover
  have hX : ∀ i, 2 ≤ X i := by
    intro i
    have hx := (mem_Ico.mp (mem_regularStarts.mp (hreg i)).1).1
    omega
  have hinj : ∀ i, Function.Injective (evenSquareClassMap (X i) L) := fun i ↦
    PaperP1.TwoPointSquareClasses.injective_evenMap_of_rank (X i) L (mem_regularStarts.mp (hreg i)).2
  have hcut := cutoff_bounds hC₀ L
  have hD := (SharedPrimeCover.cover_iff_shared (fun i ↦ (show 1 ≤ X i by have h := hX i; omega)) hcut.1 D).mpr hcover
  obtain ⟨hcost, hrank⟩ := finite_rank_bound hX hcut.1 hinj hpair D hD
  have hreal : (Module.finrank F₂ (CoordinateRestrictionRank.zeroed (relativeSpace X L) D) : ℝ) ≤
      fullCount X L (cutoff C₀ L) D + 3 * ((primeCount (cutoff C₀ L) : ℝ) + 2) := by exact_mod_cast hrank
  have hbudget := CoverRankPrimeBudget.finite_budget (hlarge N hN L hband) hcut.1 hcut.2
  exact ⟨hcost, by linarith, fun c hc ↦ ⟨component_product_supported hX hcut.1 hD c hc,
    component_product_square_small hX hcut.1 hD c hc⟩⟩

end PaperP1.TripleCoverRank
