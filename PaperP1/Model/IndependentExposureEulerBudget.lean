module

public import PaperP1.Arithmetic.EulerPrimeCovers
public import PaperP1.Asymptotics.IndependentExposurePrimePool
public import PaperP1.Arithmetic.BranchingExceptional
public import PaperP1.Arithmetic.NormalizedWindowSets

/-! # Actual source-pool factorization and weighted exceptional rows, with arbitrary many preceding windows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IndependentExposureEulerBudget

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.DefectCounting PaperP1.SmoothSquarefreeCount
  PaperP1.ConditionalWindowRank PaperP1.OldValuePrimeBudget PaperP1.IndependentExposurePrimePool

def roughPrimes (N L : ℕ) : Finset ℕ := (smallPrimesUpTo (3 * N)).filter fun p ↦ cutoff (L + 1) < p

def newPrimes (N L x : ℕ) : Finset ℕ :=
  univ.biUnion fun i : Fin (L + 1) ↦ (roughPrimes N L).filter fun p ↦ p ∣ x - 1 + i.val

def windowEuler (N L x : ℕ) : ℝ := WindowEulerAverage.windowProduct (roughPrimes N L) (L + 1) x

def rowConstant (N L : ℕ) (S : Finset ℕ) (M : ℝ) : ℝ :=
  (M / N) * (((L + 1 : ℕ) : ℝ) / 2) * Real.sqrt (3 * N : ℕ) * baseEuler S L

theorem new_euler_bound (N L x : ℕ) : eulerProduct (newPrimes N L x) (1 / 2) ≤ windowEuler N L x :=
  EulerPrimeCovers.biUnion univ (fun i : Fin (L + 1) ↦ (roughPrimes N L).filter fun p ↦ p ∣ x - 1 + i.val)

theorem window_one_le (N L x : ℕ) : 1 ≤ windowEuler N L x :=
  EulerPrimeCovers.window_one_le _ _ _

theorem pool_covered (S A : Finset ℕ) (N L : ℕ) (hN : 2 ≤ N) (hLN : L ≤ N) (hA : A ⊆ dyadicBlock N) :
    primePool (rawValues (S ∪ A) L) (L + 1) ⊆ basePrimes S L ∪ A.biUnion (newPrimes N L) := by
  intro p hp
  have hpp := primePool_prime _ _ _ hp
  have hBcut : L + 1 ≤ cutoff (L + 1) := by dsimp [cutoff]; nlinarith
  by_cases hcut : p ≤ cutoff (L + 1)
  · exact mem_union_left _ (mem_union_right _ (mem_smallPrimesUpTo.mpr ⟨hpp, hcut⟩))
  · rcases mem_union.mp hp with hsmall | hold
    · exact False.elim (hcut ((mem_smallPrimesUpTo.mp hsmall).2.trans hBcut))
    · obtain ⟨n, hn, hpn⟩ := mem_biUnion.mp hold
      obtain ⟨x, hx, hnval⟩ := mem_biUnion.mp hn
      rcases mem_union.mp hx with hxS | hxA
      · apply mem_union_left
        apply mem_union_left
        apply mem_union_right
        exact mem_biUnion.mpr ⟨n, mem_biUnion.mpr ⟨x, hxS, hnval⟩, hpn⟩
      · have hxn : 0 < x := by have h := (mem_Ico.mp (hA hxA)).1; omega
        have hnnew : n ∈ rawValues A L := mem_biUnion.mpr ⟨x, hxA, hnval⟩
        obtain ⟨hnpos, hnhi⟩ := rawValues_bounds hA hN hLN hnnew
        have hphi : p ≤ 3 * N := (Nat.le_of_dvd hnpos (Nat.dvd_of_mem_primeFactors hpn)).trans hnhi
        have hpR : p ∈ roughPrimes N L :=
          mem_filter.mpr ⟨mem_smallPrimesUpTo.mpr ⟨hpp, hphi⟩, lt_of_not_ge hcut⟩
        have hnvalues : n ∈ NormalizedWindowSets.values x L := (NormalizedWindowSets.values_eq_interval hxn).symm ▸ hnval
        obtain ⟨i, hi⟩ := NormalizedWindowSets.mem_values.mp hnvalues
        rw [startCompleteVertexLabel_eq_offset hxn] at hi
        apply mem_union_right
        apply mem_biUnion.mpr
        refine ⟨x, hxA, mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr ⟨hpR, ?_⟩⟩⟩
        rw [hi]
        exact Nat.dvd_of_mem_primeFactors hpn

theorem pool_factorization (S A : Finset ℕ) (N L : ℕ) (hN : 2 ≤ N) (hLN : L ≤ N) (hA : A ⊆ dyadicBlock N) :
    eulerProduct (primePool (rawValues (S ∪ A) L) (L + 1)) (1 / 2) ≤
      baseEuler S L * ∏ x ∈ A, windowEuler N L x := by
  apply (EulerPrimeCovers.cover _ (basePrimes S L) A (newPrimes N L) (pool_covered S A N L hN hLN hA)).trans
  exact mul_le_mul_of_nonneg_left (prod_le_prod₀ (fun _ _ ↦ eulerProduct_nonneg _ _)
    (fun x _ ↦ new_euler_bound N L x)) (eulerProduct_nonneg _ _)

theorem first_moment (N L : ℕ) (hN : 2 ≤ N) (hLN : L ≤ N) :
    (∑ x ∈ dyadicBlock N, windowEuler N L x) ≤ (3 * N : ℕ) * Real.exp 2 := by
  apply WindowEulerAverage.first_moment (L + 1) N hN (by omega) (by omega)
  · intro p hp
    exact (mem_smallPrimesUpTo.mp (mem_filter.mp hp).1).1
  · intro p hp
    exact (mem_filter.mp hp).2

theorem weighted_first_moment (N L : ℕ) (hN : 2 ≤ N) (hLN : L ≤ N)
    (w : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hcap : ∀ x ∈ dyadicBlock N, w x ≤ M / N) :
    (∑ x ∈ dyadicBlock N, w x * windowEuler N L x) ≤ 3 * M * Real.exp 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ ∑ x ∈ dyadicBlock N, (M / N) * windowEuler N L x := sum_le_sum
      (fun x hx ↦ mul_le_mul_of_nonneg_right (hcap x hx) (by have h := window_one_le N L x; linarith))
    _ = (M / N) * ∑ x ∈ dyadicBlock N, windowEuler N L x := (mul_sum _ _ _).symm
    _ ≤ (M / N) * ((3 * N : ℕ) * Real.exp 2) :=
      mul_le_mul_of_nonneg_left (first_moment N L hN hLN) (div_nonneg hM hn.le)
    _ = _ := by push_cast; field_simp

theorem weighted_bad_row (S A : Finset ℕ) (N L : ℕ) (hN : 2 ≤ N) (hLN : L ≤ N) (hA : A ⊆ dyadicBlock N)
    (w : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hcap : ∀ x ∈ dyadicBlock N, w x ≤ M / N) :
    (∑ x ∈ BranchingExceptional.badStarts N L (rawValues (S ∪ A) L), w x) ≤
      rowConstant N L S M * ∏ x ∈ A, windowEuler N L x := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let R := rawValues (S ∪ A) L
  have hcount : ((BranchingExceptional.badStarts N L R).card : ℝ) ≤
      (((L + 1 : ℕ) : ℝ) / 2) * Real.sqrt (3 * N : ℕ) * eulerProduct (primePool R (L + 1)) (1 / 2) := by
    have hpool := card_naturalValues_le_euler (primePool R (L + 1))
      (fun p hp ↦ (primePool_prime _ _ _ hp).one_lt.le) (3 * N) (1 / 2) le_rfl
    rw [← Real.sqrt_eq_rpow] at hpool
    exact (BranchingExceptional.badStarts_card_half R hN hLN).trans
      ((mul_le_mul_of_nonneg_left hpool (by positivity)).trans_eq (mul_assoc _ _ _).symm)
  calc
    _ ≤ (M / N) * (BranchingExceptional.badStarts N L R).card := by
      calc
        _ ≤ ∑ _x ∈ BranchingExceptional.badStarts N L R, M / N := sum_le_sum
          (fun x hx ↦ hcap x (BranchingExceptional.badStarts_subset _ _ _ hx))
        _ = _ := by rw [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ (M / N) * ((((L + 1 : ℕ) : ℝ) / 2) * Real.sqrt (3 * N : ℕ) *
        eulerProduct (primePool R (L + 1)) (1 / 2)) := mul_le_mul_of_nonneg_left hcount (div_nonneg hM hn.le)
    _ = ((M / N) * (((L + 1 : ℕ) : ℝ) / 2) * Real.sqrt (3 * N : ℕ)) *
        eulerProduct (primePool R (L + 1)) (1 / 2) := by ring
    _ ≤ ((M / N) * (((L + 1 : ℕ) : ℝ) / 2) * Real.sqrt (3 * N : ℕ)) *
        (baseEuler S L * ∏ x ∈ A, windowEuler N L x) := mul_le_mul_of_nonneg_left
          (pool_factorization S A N L hN hLN hA) (by positivity)
    _ = _ := by unfold rowConstant; ring

end PaperP1.IndependentExposureEulerBudget
