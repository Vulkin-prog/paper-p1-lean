module

public import PaperP1.Arithmetic.AdjacentSquareDivisibility
public import PaperP1.Arithmetic.SquarefreeKernelProducts
public import PaperP1.Arithmetic.KernelSquareBudget
public import PaperP1.Combinatorics.FiniteCoverCount
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # Explicit finite lower bounds for two individually small neighboring odd kernels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoAdjacentSmallKernels

open Finset PaperP1.SmallPrimeBudget PaperP1.DefectivePredicate PaperP1.LargeOddKernel
  PaperP1.CoprimeIntervalPairs PaperP1.AdjacentSquareDivisibility

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def admissible (N H : ℕ) (T : ℝ) : Finset ℕ :=
  (Ico N (2 * N)).filter fun n ↦ (largeOddKernel H n : ℝ) ≤ T ∧ (largeOddKernel H (n + 1) : ℝ) ≤ T

abbrev Code := Σ _p : ℕ × ℕ, ℕ

def incidences (N D : ℕ) : Finset Code := (intervalPairs D).sigma fun p ↦ solutions N p.1 p.2

theorem square_divisor_budget {n d : ℕ} (H : ℕ) (hn : 0 < n) (hd : 0 < d) (hdiv : d ^ 2 ∣ n) :
    largeOddKernel H n * d ^ 2 ≤ n := by
  obtain ⟨u, hu⟩ := hdiv
  have huPos : 0 < u := by
    by_contra hh
    have hz : u = 0 := by omega
    rw [hz, mul_zero] at hu
    omega
  have hsf : squarefreeKernel n = squarefreeKernel u := by
    rw [hu, Nat.mul_comm]
    exact SquarefreeKernelProducts.kernel_mul_square u d huPos.ne' hd.ne'
  have hpart : 0 < canonicalSquarePart u ^ 2 :=
    pow_pos (Nat.pos_of_ne_zero (SquarefreeKernelProducts.canonical_part_ne_zero u huPos.ne')) 2
  have hsmall : squarefreeKernel u ≤ u := by
    have hh := Nat.le_mul_of_pos_right (squarefreeKernel u) hpart
    rwa [squarefreeKernel_mul_squarePart huPos.ne'] at hh
  have hk : largeOddKernel H n ≤ u := (KernelSquareBudget.large_kernel_le_squarefree H n).trans
    (hsf ▸ hsmall)
  calc
    _ ≤ u * d ^ 2 := Nat.mul_le_mul_right _ hk
    _ = n := by rw [hu]; ring

theorem incidences_lower {N D : ℕ} (hD : 0 < D) (hN : 40000 * D ^ 4 ≤ N) :
    (N : ℝ) / (4000 * (D : ℝ) ^ 2) ≤ ((incidences N D).card : ℝ) := by
  let Q := 10000 * D ^ 4
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hNQ : 4 * Q ≤ N := by dsimp [Q]; nlinarith only [hN]
  have hsol (p : ℕ × ℕ) (hp : p ∈ intervalPairs D) :
      (N : ℝ) / (2 * Q) ≤ ((solutions N p.1 p.2).card : ℝ) := by
    obtain ⟨hd, he, _hloD, hdhi, _hloE, hehi, hcop⟩ := intervalPairs_data hp
    have hprod := Nat.mul_le_mul (Nat.pow_le_pow_left hdhi 2) (Nat.pow_le_pow_left hehi 2)
    have hcap : p.1 ^ 2 * p.2 ^ 2 ≤ Q := by dsimp [Q]; nlinarith only [hprod]
    exact uniform_solutions_card_lower hd he hcop hQ hcap hNQ
  calc
    _ = (5 * (D : ℝ) ^ 2) * ((N : ℝ) / (2 * Q)) := by
      dsimp [Q]
      push_cast
      field_simp
      ring
    _ ≤ ((intervalPairs D).card : ℝ) * ((N : ℝ) / (2 * Q)) :=
      mul_le_mul_of_nonneg_right (intervalPairs_card_lower D) (by positivity)
    _ = ∑ _p ∈ intervalPairs D, (N : ℝ) / (2 * Q) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ intervalPairs D, ((solutions N p.1 p.2).card : ℝ) := sum_le_sum hsol
    _ = _ := by rw [incidences, card_sigma, Nat.cast_sum]

theorem fibre_card {N D n : ℕ} (hn : 0 < n) :
    ((incidences N D).filter fun p ↦ p.2 = n).card ≤ n.divisors.card * (n + 1).divisors.card := by
  have hinj : Set.InjOn (fun p : Code ↦ p.1) (((incidences N D).filter fun p ↦ p.2 = n) : Set Code) := by
    intro p hp q hq hh
    exact Sigma.ext hh (heq_of_eq ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm))
  have hmap (p : Code) (hp : p ∈ (incidences N D).filter fun p ↦ p.2 = n) :
      p.1 ∈ n.divisors ×ˢ (n + 1).divisors := by
    obtain ⟨hinc, heq⟩ := mem_filter.mp hp
    obtain ⟨_hpair, hsol⟩ := mem_sigma.mp hinc
    have hdiv := (mem_filter.mp hsol).2
    rw [heq] at hdiv
    have hd : p.1.1 ∣ n := (show p.1.1 ∣ p.1.1 ^ 2 from ⟨p.1.1, by ring⟩).trans hdiv.1
    have he : p.1.2 ∣ n + 1 := (show p.1.2 ∣ p.1.2 ^ 2 from ⟨p.1.2, by ring⟩).trans hdiv.2
    exact mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hd, hn.ne'⟩, Nat.mem_divisors.mpr ⟨he, by omega⟩⟩
  simpa only [card_product] using card_le_card_of_injOn (fun p : Code ↦ p.1) hmap hinj

theorem incidence_admissible {N D H : ℕ} {T : ℝ} (hN : 0 < N) (hT : 0 ≤ T)
    (hbudget : 2 * (N : ℝ) ≤ T * (D : ℝ) ^ 2) {p : Code} (hp : p ∈ incidences N D) :
    p.2 ∈ admissible N H T := by
  obtain ⟨hpair, hsol⟩ := mem_sigma.mp hp
  obtain ⟨hd, he, hDd, _hdhi, hDe, _hehi, _hcop⟩ := intervalPairs_data hpair
  obtain ⟨hinterval, hdivD, hdivE⟩ := mem_filter.mp hsol
  have hn : 0 < p.2 := hN.trans_le (mem_Ico.mp hinterval).1
  have hnHi : p.2 ≤ 2 * N := (mem_Ico.mp hinterval).2.le
  have hn1Hi : p.2 + 1 ≤ 2 * N := by have := (mem_Ico.mp hinterval).2; omega
  have hsingle (n d : ℕ) (hn0 : 0 < n) (hd0 : 0 < d) (hDd0 : D ≤ d)
      (hnN : n ≤ 2 * N) (hdiv : d ^ 2 ∣ n) : (largeOddKernel H n : ℝ) ≤ T := by
    have hker : (largeOddKernel H n : ℝ) * (d : ℝ) ^ 2 ≤ n := by
      exact_mod_cast square_divisor_budget H hn0 hd0 hdiv
    have hDpow := pow_le_pow_left₀ (Nat.cast_nonneg D) (by exact_mod_cast hDd0 : (D : ℝ) ≤ d) 2
    have hmul := mul_le_mul_of_nonneg_left hDpow hT
    have hhi : (n : ℝ) ≤ 2 * N := by exact_mod_cast hnN
    apply (mul_le_mul_iff_left₀ (by positivity : (0 : ℝ) < (d : ℝ) ^ 2)).mp
    exact hker.trans (hhi.trans (hbudget.trans hmul))
  exact mem_filter.mpr ⟨hinterval, hsingle p.2 p.1.1 hn hd hDd hnHi hdivD,
    hsingle (p.2 + 1) p.1.2 (by omega) he hDe hn1Hi hdivE⟩

theorem incidences_upper {N D H : ℕ} {T K : ℝ} (hN : 0 < N) (hT : 0 ≤ T)
    (hbudget : 2 * (N : ℝ) ≤ T * (D : ℝ) ^ 2)
    (hdivisors : ∀ n ∈ Ico N (2 * N), (n.divisors.card : ℝ) * (n + 1).divisors.card ≤ K) :
    ((incidences N D).card : ℝ) ≤ ((admissible N H T).card : ℝ) * K := by
  apply FiniteCoverCount.cardinal_le (incidences N D) (admissible N H T)
    (fun n ↦ (incidences N D).filter fun p ↦ p.2 = n) K
  · intro p hp
    exact ⟨p.2, incidence_admissible hN hT hbudget hp, mem_filter.mpr ⟨hp, rfl⟩⟩
  · intro n hn
    have hinterval := (mem_filter.mp hn).1
    have hn0 : 0 < n := hN.trans_le (mem_Ico.mp hinterval).1
    exact (by exact_mod_cast fibre_card (N := N) (D := D) hn0 :
      (((incidences N D).filter fun p ↦ p.2 = n).card : ℝ) ≤ (n.divisors.card : ℝ) * (n + 1).divisors.card).trans
        (hdivisors n hinterval)

theorem finite_lower {N D H : ℕ} {T K : ℝ} (hN : 0 < N) (hD : 0 < D) (hT : 0 ≤ T)
    (hlarge : 40000 * D ^ 4 ≤ N) (hbudget : 2 * (N : ℝ) ≤ T * (D : ℝ) ^ 2)
    (hdivisors : ∀ n ∈ Ico N (2 * N), (n.divisors.card : ℝ) * (n + 1).divisors.card ≤ K) :
    (N : ℝ) / (4000 * (D : ℝ) ^ 2) ≤ ((admissible N H T).card : ℝ) * K :=
  (incidences_lower hD hlarge).trans (incidences_upper hN hT hbudget hdivisors)

end PaperP1.TwoAdjacentSmallKernels
