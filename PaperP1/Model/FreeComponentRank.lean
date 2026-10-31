module

public import PaperP1.Affine.SmallPrimePairConstraints
public import PaperP1.Combinatorics.LargePrimeComponentArithmetic
public import PaperP1.Model.RegularSetAsymptotic
public import PaperP1.Arithmetic.ComponentPrimeBudget

/-! # Comparison of free components with the actual pair intersection rank -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FreeComponentRank

open Filter PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
open LocalDefectBound LargePrimeGraph LargePrimeGraphResolution LargePrimeComponentArithmetic
open RegularSetAsymptotic CriticalBandScale Finset

local instance freeComponentRankPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def pairIntersectionRank (x y L : ℕ) : ℕ :=
  Module.finrank F₂ (squareClassSpace x L ⊓ squareClassSpace y L : Submodule F₂ (ℕ →₀ F₂))

theorem intersection_le_components_add_defects {x y L : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    pairIntersectionRank x y L ≤ nontrivialComponentCount x y L + defectiveVertexCount x y L := by
  have hfull := finrank_completeRelationCode x y L
  have hupper := complete_relation_rank_le_large x y L
  rw [finrank_largePrimeSolution_eq_defective_add_components hx hy] at hupper
  dsimp [pairIntersectionRank]
  omega

theorem components_le_intersection_add_cost {x y L : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hrx : Module.finrank F₂ (LinearMap.ker (evenSquareClassMap x L)) ≤ 1)
    (hry : Module.finrank F₂ (LinearMap.ker (evenSquareClassMap y L)) ≤ 1) :
    nontrivialComponentCount x y L ≤ pairIntersectionRank x y L + primeCount (10 * (L + 1)) + 4 := by
  have hfull := finrank_completeRelationCode x y L
  have hcost := large_relation_rank_le_complete_add_cost x y L
  rw [finrank_largePrimeSolution_eq_defective_add_components hx hy] at hcost
  dsimp [pairIntersectionRank]
  omega

theorem component_intersection_abs_bound {x y L : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hrx : Module.finrank F₂ (LinearMap.ker (evenSquareClassMap x L)) ≤ 1)
    (hry : Module.finrank F₂ (LinearMap.ker (evenSquareClassMap y L)) ≤ 1) :
    |(nontrivialComponentCount x y L : ℝ) - pairIntersectionRank x y L| ≤
      (defectiveVertexCount x y L : ℝ) + primeCount (10 * (L + 1)) + 4 := by
  have hd : (pairIntersectionRank x y L : ℝ) ≤
      (nontrivialComponentCount x y L : ℝ) + defectiveVertexCount x y L := by
    exact_mod_cast intersection_le_components_add_defects hx hy
  have hc : (nontrivialComponentCount x y L : ℝ) ≤
      (pairIntersectionRank x y L : ℝ) + primeCount (10 * (L + 1)) + 4 := by
    exact_mod_cast components_le_intersection_add_cost hx hy hrx hry
  have hD : (0 : ℝ) ≤ defectiveVertexCount x y L := Nat.cast_nonneg _
  have hπ : (0 : ℝ) ≤ primeCount (10 * (L + 1)) := Nat.cast_nonneg _
  apply abs_le.mpr
  constructor <;> linarith

/-- Exact T9.3 rate, with one constant before the fixed critical-band width.
All pairs of dyadic starts, including overlapping physical windows, are included. -/
theorem companion_T9_3 :
    ∃ K : ℝ, 0 < K ∧ ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ dyadicBlock N, ∀ y ∈ dyadicBlock N,
        |(nontrivialComponentCount x y L : ℝ) - pairIntersectionRank x y L| ≤
          K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨KD, hKD, hdef⟩ := defectiveVertexCount_critical_bound
  obtain ⟨B₀, hB₀, hprime⟩ := ComponentPrimeBudget.prime_constraint_cost_eventually
  refine ⟨KD + 24, by linarith, fun C ↦ ?_⟩
  obtain ⟨Ndef, hNdef⟩ := hdef C
  obtain ⟨Nrank, hNrank⟩ := dyadic_critical_relation_rank_le_one C
  obtain ⟨Nscale, hNscale⟩ := critical_band_scale C
  obtain ⟨Nlog, hNlog⟩ := eventually_atTop.mp
    (PrimeLogBudget.log_nat_tendsto_atTop.eventually
      (eventually_ge_atTop ((B₀ : ℝ) / lowerScale)))
  refine ⟨max 2 (max Ndef (max Nrank (max Nscale Nlog))), ?_⟩
  intro N hN L hband x hx y hy
  have hxpos : 0 < x := by have := (mem_Ico.mp hx).1; omega
  have hypos : 0 < y := by have := (mem_Ico.mp hy).1; omega
  have hxrank := hNrank N (by omega) L hband x hx
  have hyrank := hNrank N (by omega) L hband y hy
  have hrx : Module.finrank F₂ (LinearMap.ker (evenSquareClassMap x L)) ≤ 1 := by
    rw [← (LocalRunRank.relationEvenEquiv (L := L) hxpos).finrank_eq]
    exact hxrank
  have hry : Module.finrank F₂ (LinearMap.ker (evenSquareClassMap y L)) ≤ 1 := by
    rw [← (LocalRunRank.relationEvenEquiv (L := L) hypos).finrank_eq]
    exact hyrank
  have hsc := (hNscale N (by omega) L hband).1
  have hblog : (B₀ : ℝ) ≤ lowerScale * Real.log N := by
    have h := (div_le_iff₀ lowerScale_pos).mp (hNlog N (by omega))
    nlinarith
  have hB : B₀ ≤ L + 1 := by exact_mod_cast hblog.trans hsc
  have hp := hprime (L + 1) hB
  have hD := hNdef N (by omega) L hband x hx y hy
  calc
    _ ≤ (defectiveVertexCount x y L : ℝ) + primeCount (10 * (L + 1)) + 4 :=
      component_intersection_abs_bound (by omega) (by omega) hrx hry
    _ ≤ KD * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) +
        24 * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) := by linarith
    _ = _ := by ring

end PaperP1.FreeComponentRank
