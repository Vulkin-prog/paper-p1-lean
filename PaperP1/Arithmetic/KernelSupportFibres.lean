module

public import PaperP1.Arithmetic.SmallKernelCount
public import PaperP1.Arithmetic.TruncatedKernelProducts
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Weighted fibres of the actual small and large odd-prime supports

The canonical support-triple argument is adapted and generalized from
`PaperC/Arithmetic/LargeKernelWeightedCounting.lean`, Vulkin-prog, Apache-2.0,
commit b9fa9ba490f201b408a302a86f1594ee620b228b,
Git blob 0a767c88c4899fbb1fc4996c6a5188a5c19af103.
The weight is arbitrary and nonnegative; no asymptotic estimate is assumed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.KernelSupportFibres

open Finset PaperP1.Arithmetic PaperP1.DefectCounting PaperP1.DefectivePredicate
open PaperP1.SmallPrimeBudget PaperP1.LargeOddKernel PaperP1.TruncatedKernelProducts

def roughSupport (B n : ℕ) : Finset ℕ := (oddPrimeSupport n).filter (B < ·)

def roughPrimes (B X : ℕ) : Finset ℕ := (smallPrimesUpTo X).filter (B < ·)

theorem mem_roughPrimes {B X p : ℕ} :
    p ∈ roughPrimes B X ↔ Nat.Prime p ∧ p ≤ X ∧ B < p := by
  simp only [roughPrimes, mem_filter, mem_smallPrimesUpTo, and_assoc]

theorem support_product (B n : ℕ) : (roughSupport B n).prod id = largeOddKernel B n := rfl

theorem support_subset {B X n : ℕ} (hn : 0 < n) (hnX : n ≤ X) :
    roughSupport B n ⊆ roughPrimes B X := by
  intro p hp
  obtain ⟨hp, hBp⟩ := mem_filter.mp hp
  exact mem_roughPrimes.mpr ⟨prime_of_mem_oddPrimeSupport hp,
    (Nat.le_of_dvd hn (dvd_of_mem_oddPrimeSupport hp)).trans hnX, hBp⟩

abbrev Triple := Σ _s : Finset ℕ, Σ _r : Finset ℕ, ℕ

def canonical (B n : ℕ) : Triple :=
  ⟨smallOddSupport B n, roughSupport B n, canonicalSquarePart n⟩

def candidates (B X : ℕ) : Finset Triple :=
  (smallPrimesUpTo B).powerset.sigma fun s ↦
    (roughPrimes B X).powerset.sigma fun r ↦
      Finset.Icc 1 (Nat.sqrt (X / (s.prod id * r.prod id)))

theorem decomposition {n : ℕ} (hn : n ≠ 0) (B : ℕ) :
    n = canonicalSquarePart n ^ 2 *
      (smallOddSupport B n).prod id * (roughSupport B n).prod id := by
  rw [support_product, ← smallOddPart, mul_assoc, small_mul_large,
    mul_comm, squarefreeKernel_mul_squarePart hn]

theorem canonical_injective {B m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : canonical B m = canonical B n) : m = n := by
  have hs := congrArg (fun t : Triple ↦ t.1) h
  have hr := congrArg (fun t : Triple ↦ t.2.1) h
  have ha := congrArg (fun t : Triple ↦ t.2.2) h
  change smallOddSupport B m = smallOddSupport B n at hs
  change roughSupport B m = roughSupport B n at hr
  change canonicalSquarePart m = canonicalSquarePart n at ha
  rw [decomposition hm B, decomposition hn B, hs, hr, ha]

theorem canonical_mem {B X n : ℕ} (hn : n ∈ Finset.Icc 1 X) :
    canonical B n ∈ candidates B X := by
  obtain ⟨hn, hnX⟩ := mem_Icc.mp hn
  have hn0 : n ≠ 0 := by omega
  have ha : 0 < canonicalSquarePart n := by
    by_contra h
    have hz : canonicalSquarePart n = 0 := by omega
    have heq := decomposition hn0 B
    rw [hz, zero_pow (by decide : 2 ≠ 0), zero_mul, zero_mul] at heq
    omega
  have hd : 0 < (smallOddSupport B n).prod id * (roughSupport B n).prod id :=
    Nat.mul_pos (smallOddPart_pos B n) (largeOddKernel_pos B n)
  have haX : canonicalSquarePart n ^ 2 ≤
      X / ((smallOddSupport B n).prod id * (roughSupport B n).prod id) := by
    apply (Nat.le_div_iff_mul_le hd).mpr
    rw [← mul_assoc, ← decomposition hn0 B]
    exact hnX
  exact mem_sigma.mpr ⟨mem_powerset.mpr (smallOddSupport_subset B n),
    mem_sigma.mpr ⟨mem_powerset.mpr (support_subset hn hnX),
      mem_Icc.mpr ⟨ha, (Nat.le_sqrt').mpr haX⟩⟩⟩

theorem weighted_fibres (B X : ℕ) (f : Finset ℕ → Finset ℕ → ℝ)
    (hf : ∀ s r, 0 ≤ f s r) :
    (∑ n ∈ Finset.Icc 1 X, f (smallOddSupport B n) (roughSupport B n)) ≤
      ∑ s ∈ (smallPrimesUpTo B).powerset, ∑ r ∈ (roughPrimes B X).powerset,
        (Nat.sqrt (X / (s.prod id * r.prod id)) : ℝ) * f s r := by
  let g : Triple → ℝ := fun t ↦ f t.1 t.2.1
  have hsum : (∑ n ∈ Finset.Icc 1 X, f (smallOddSupport B n) (roughSupport B n)) =
      ∑ t ∈ (Finset.Icc 1 X).image (canonical B), g t := by
    rw [sum_image]
    · rfl
    · intro m hm n hn h
      exact canonical_injective (by have := (mem_Icc.mp hm).1; omega)
        (by have := (mem_Icc.mp hn).1; omega) h
  have hsub : (Finset.Icc 1 X).image (canonical B) ⊆ candidates B X := by
    intro t ht
    obtain ⟨n, hn, rfl⟩ := mem_image.mp ht
    exact canonical_mem hn
  calc
    _ = _ := hsum
    _ ≤ ∑ t ∈ candidates B X, g t :=
      sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ ↦ hf t.1 t.2.1)
    _ = _ := by
      rw [candidates, sum_sigma]
      apply sum_congr rfl
      intro s _
      rw [sum_sigma]
      apply sum_congr rfl
      intro r _
      simp [g, Nat.card_Icc]

end PaperP1.KernelSupportFibres
