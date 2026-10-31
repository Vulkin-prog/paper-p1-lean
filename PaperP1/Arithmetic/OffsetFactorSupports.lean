module

public import PaperP1.Arithmetic.FiniteEulerRankin
public import Mathlib.Data.Nat.Squarefree

/-! # Literal squarefree values and arbitrary distinct factor supports -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetFactorSupports

open Finset PaperP1.DefectCounting PaperP1.FiniteEulerRankin

def primePool (Y X : ℝ) : Finset ℕ :=
  (smallPrimesUpTo (Nat.floor X)).filter fun p : ℕ ↦ Y < (p : ℝ)

def roughValues (Y X : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor X)).filter fun n ↦ Squarefree n ∧ ∀ p ∈ n.primeFactors, Y < (p : ℝ)

def roughWeightedCount (Y X a : ℝ) : ℝ := ∑ n ∈ roughValues Y X, a ^ n.primeFactors.card

def integerPool (Y X : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor X)).filter fun n : ℕ ↦ Y < (n : ℝ)

def integerSupports (Y X : ℝ) : Finset (Finset ℕ) := admissibleSupports (integerPool Y X) X

def integerWeightedCount (Y X a : ℝ) : ℝ := weightedCount (integerPool Y X) X a

theorem roughWeightedCount_eq_source (Y X r : ℝ) (d : ℕ) :
    roughWeightedCount Y X (r ^ d) = ∑ n ∈ roughValues Y X, r ^ (d * n.primeFactors.card) := by
  simp only [roughWeightedCount, pow_mul]

theorem integerWeightedCount_eq_source (Y X r : ℝ) (d : ℕ) :
    integerWeightedCount Y X (r ^ d) = ∑ A ∈ integerSupports Y X, r ^ (d * A.card) := by
  simp only [integerWeightedCount, weightedCount, integerSupports, pow_mul]

theorem mem_primePool {Y X : ℝ} {p : ℕ} :
    p ∈ primePool Y X ↔ Nat.Prime p ∧ p ≤ Nat.floor X ∧ Y < (p : ℝ) := by
  simp only [primePool, mem_filter, mem_smallPrimesUpTo, and_assoc]

theorem mem_roughValues (Y X : ℝ) (hX : 0 ≤ X) (n : ℕ) :
    n ∈ roughValues Y X ↔ 1 ≤ n ∧ (n : ℝ) ≤ X ∧ Squarefree n ∧
      ∀ p ∈ n.primeFactors, Y < (p : ℝ) := by
  simp only [roughValues, mem_filter, mem_Icc, Nat.le_floor_iff hX, and_assoc]

theorem primeFactors_injective_on_rough (Y X : ℝ) :
    Set.InjOn (fun n : ℕ ↦ n.primeFactors) (roughValues Y X : Set ℕ) := by
  intro i hi j hj hij
  have hiS := (mem_filter.mp hi).2.1
  have hjS := (mem_filter.mp hj).2.1
  calc
    i = i.primeFactors.prod id := (Nat.prod_primeFactors_of_squarefree hiS).symm
    _ = j.primeFactors.prod id := congrArg (fun S : Finset ℕ ↦ S.prod id) hij
    _ = j := Nat.prod_primeFactors_of_squarefree hjS

theorem rough_primeFactors_mem (Y X : ℝ) (hX : 0 ≤ X) (n : ℕ) (hn : n ∈ roughValues Y X) :
    n.primeFactors ∈ admissibleSupports (primePool Y X) X := by
  obtain ⟨hnpos, hnX, hs, hrough⟩ := (mem_roughValues Y X hX n).mp hn
  apply mem_admissibleSupports.mpr
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨hpprime, hpdvd, _⟩ := Nat.mem_primeFactors.mp hp
    have hpn : p ≤ n := Nat.le_of_dvd hnpos hpdvd
    apply mem_primePool.mpr
    exact ⟨hpprime, (Nat.le_floor_iff hX).mpr ((by exact_mod_cast hpn : (p : ℝ) ≤ n).trans hnX),
      hrough p hp⟩
  · have heq : n.primeFactors.prod id = n := Nat.prod_primeFactors_of_squarefree hs
    rw [heq]
    exact hnX

theorem roughWeightedCount_le_supports (Y X a : ℝ) (hX : 0 ≤ X) (ha : 0 ≤ a) :
    roughWeightedCount Y X a ≤ weightedCount (primePool Y X) X a := by
  have hsub : (roughValues Y X).image (fun n : ℕ ↦ n.primeFactors) ⊆
      admissibleSupports (primePool Y X) X := by
    intro S hS
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hS
    exact rough_primeFactors_mem Y X hX n hn
  have heq : (∑ S ∈ (roughValues Y X).image (fun n : ℕ ↦ n.primeFactors), a ^ S.card) =
      roughWeightedCount Y X a := by
    rw [sum_image (primeFactors_injective_on_rough Y X)]
    rfl
  rw [← heq]
  exact sum_le_sum_of_subset_of_nonneg hsub (fun S _ _ ↦ pow_nonneg ha S.card)

theorem mem_integerPool {Y X : ℝ} {n : ℕ} :
    n ∈ integerPool Y X ↔ 1 ≤ n ∧ n ≤ Nat.floor X ∧ Y < (n : ℝ) := by
  simp only [integerPool, mem_filter, mem_Icc, and_assoc]

/-- Every finite support in the source sum occurs in this finite population. -/
theorem mem_integerSupports (Y X : ℝ) (hY : 1 ≤ Y) (hX : 0 ≤ X) (A : Finset ℕ) :
    A ∈ integerSupports Y X ↔ (∀ g ∈ A, Y < (g : ℝ)) ∧ (↑(A.prod id) : ℝ) ≤ X := by
  rw [integerSupports, mem_admissibleSupports]
  constructor
  · rintro ⟨hsub, hprod⟩
    exact ⟨fun g hg ↦ (mem_integerPool.mp (hsub hg)).2.2, hprod⟩
  · rintro ⟨hrough, hprod⟩
    have hpos (g : ℕ) (hg : g ∈ A) : 1 ≤ g := by
      have h : (1 : ℝ) < g := hY.trans_lt (hrough g hg)
      exact_mod_cast h.le
    refine ⟨?_, hprod⟩
    intro g hg
    have hgprod : g ≤ A.prod id := single_le_prod hpos hg
    apply mem_integerPool.mpr
    exact ⟨hpos g hg, (Nat.le_floor_iff hX).mpr ((by exact_mod_cast hgprod : (g : ℝ) ≤ A.prod id).trans hprod),
      hrough g hg⟩

end PaperP1.OffsetFactorSupports
