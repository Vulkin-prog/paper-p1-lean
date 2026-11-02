module

public import PaperP1.Combinatorics.DisjointColumnWeights
public import PaperP1.Combinatorics.LargePrimeComponentArithmetic
public import PaperP1.Combinatorics.IntervalMultiples
public import Mathlib.Data.Nat.Cast.Order.Field

/-! # Actual medium-prime columns of the disjoint large-prime components -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MediumPrimeColumns

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.LargePrimeOccurrences
  PaperP1.LargePrimeGraph PaperP1.LargePrimeComponentArithmetic

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def componentVertices {V : Type*} [Fintype V] (G : SimpleGraph V) (c : G.ConnectedComponent) : Finset V := by
  classical
  exact univ.filter (fun v ↦ G.connectedComponentMk v = c)

theorem mem_componentVertices {V : Type*} [Fintype V] (G : SimpleGraph V) (c : G.ConnectedComponent) (v : V) :
    v ∈ componentVertices G c ↔ G.connectedComponentMk v = c := by
  classical
  simp only [componentVertices, mem_filter, mem_univ, true_and]

theorem componentVertices_disjoint {V : Type*} [Fintype V] (G : SimpleGraph V)
    (Q : Finset G.ConnectedComponent) :
    (↑Q : Set G.ConnectedComponent).Pairwise (fun c d ↦ Disjoint (componentVertices G c) (componentVertices G d)) := by
  intro c _hc d _hd hne
  apply disjoint_left.mpr
  intro v hvc hvd
  exact hne (((mem_componentVertices G c v).mp hvc).symm.trans ((mem_componentVertices G d v).mp hvd))

def mediumPrimes (L z : ℕ) : Finset ℕ :=
  (range (10 * (L + 1) + 1)).filter (fun p ↦ p.Prime ∧ z < p)

theorem mem_mediumPrimes (L z p : ℕ) : p ∈ mediumPrimes L z ↔ p.Prime ∧ z < p ∧ p ≤ 10 * (L + 1) := by
  simp only [mediumPrimes, mem_filter, mem_range]
  constructor
  · rintro ⟨hL, hp, hz⟩
    exact ⟨hp, hz, by omega⟩
  · rintro ⟨hp, hz, hL⟩
    exact ⟨by omega, hp, hz⟩

def startOdd (x L p : ℕ) : Finset (Fin (L + 1)) :=
  univ.filter (fun v ↦ parityVec (startCompleteVertexLabel x L v) p ≠ 0)

def pairOdd (x y L p : ℕ) : Finset (Occurrence L) :=
  univ.filter (fun v ↦ parityVec (twoStartCompleteVertexLabel x y L v) p ≠ 0)

theorem nonzero_parity_dvd {n p : ℕ} (h : parityVec n p ≠ 0) : p ∣ n := by
  by_contra hn
  exact h (by simp only [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd hn, Nat.cast_zero])

theorem startOdd_card_le (x L p : ℕ) (hx : 0 < x) : (startOdd x L p).card ≤ (L + 1) / p + 1 := by
  classical
  have hmap : (startOdd x L p).card ≤
      ((Ico (x - 1) (x - 1 + (L + 1))).filter (fun n ↦ p ∣ n)).card := by
    apply card_le_card_of_injOn (startCompleteVertexLabel x L)
    · intro v hv
      apply mem_filter.mpr
      refine ⟨?_, nonzero_parity_dvd (mem_filter.mp hv).2⟩
      rw [startCompleteVertexLabel_eq_offset hx]
      exact mem_Ico.mpr ⟨by omega, by have := v.isLt; omega⟩
    · intro v _hv w _hw h
      exact start_label_injective hx h
  exact hmap.trans (IntervalMultiples.card_multiples_interval_le (x - 1) (L + 1) p)

theorem pairOdd_eq_disjSum (x y L p : ℕ) :
    pairOdd x y L p = (startOdd x L p).disjSum (startOdd y L p) := by
  classical
  apply Finset.ext
  intro v
  cases v with
  | inl i =>
    rw [inl_mem_disjSum]
    constructor
    · intro h
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h).2⟩
    · intro h
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h).2⟩
  | inr i =>
    rw [inr_mem_disjSum]
    constructor
    · intro h
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h).2⟩
    · intro h
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h).2⟩

theorem pairOdd_card_le (x y L p : ℕ) (hx : 0 < x) (hy : 0 < y) :
    (pairOdd x y L p).card ≤ 2 * ((L + 1) / p + 1) := by
  rw [pairOdd_eq_disjSum, card_disjSum]
  have h₁ := startOdd_card_le x L p hx
  have h₂ := startOdd_card_le y L p hy
  omega

def column (x y L z : ℕ) (c : (largePrimeGraph x y L).ConnectedComponent) : Finset ℕ :=
  DisjointColumnWeights.column (mediumPrimes L z) (componentVertices (largePrimeGraph x y L))
    (fun v p ↦ parityVec (twoStartCompleteVertexLabel x y L v) p) c

theorem actual_weight_budget (x y L z : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (hx : 0 < x) (hy : 0 < y) :
    ∑ c ∈ Q, (column x y L z c).card ≤ ∑ p ∈ mediumPrimes L z, 2 * ((L + 1) / p + 1) := by
  classical
  have hweight := DisjointColumnWeights.sum_weights_le Q (univ : Finset (Occurrence L)) (mediumPrimes L z)
    (componentVertices (largePrimeGraph x y L)) (fun v p ↦ parityVec (twoStartCompleteVertexLabel x y L v) p)
    (fun _ _ ↦ subset_univ _) (componentVertices_disjoint (largePrimeGraph x y L) Q)
  exact hweight.trans (sum_le_sum (fun p _ ↦ pairOdd_card_le x y L p hx hy))

theorem actual_weight_real (x y L z : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (hx : 0 < x) (hy : 0 < y) :
    ∑ c ∈ Q, ((column x y L z c).card : ℝ) ≤
      2 * (L + 1 : ℕ) * (∑ p ∈ mediumPrimes L z, 1 / (p : ℝ)) + 2 * (mediumPrimes L z).card := by
  have hnat := actual_weight_budget x y L z Q hx hy
  have hc : (∑ c ∈ Q, ((column x y L z c).card : ℝ)) ≤
      ∑ p ∈ mediumPrimes L z, 2 * (((L + 1) / p : ℕ) + 1 : ℝ) := by exact_mod_cast hnat
  calc
    _ ≤ ∑ p ∈ mediumPrimes L z, 2 * (((L + 1) / p : ℕ) + 1 : ℝ) := hc
    _ ≤ ∑ p ∈ mediumPrimes L z, 2 * (((L + 1 : ℕ) : ℝ) / p + 1) := by
      exact sum_le_sum (fun p _ ↦ by linarith [Nat.cast_div_le (m := L + 1) (n := p) (α := ℝ)])
    _ = _ := by
      rw [mul_sum]
      simp only [mul_add, sum_add_distrib, sum_const, nsmul_eq_mul]
      congr 1
      · apply sum_congr rfl
        intros
        ring
      · ring

theorem light_components_lower (x y L z : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (hx : 0 < x) (hy : 0 < y) :
    (Q.card : ℝ) - (2 * (L + 1 : ℕ) * (∑ p ∈ mediumPrimes L z, 1 / (p : ℝ)) +
      2 * (mediumPrimes L z).card) / 3 ≤
        ((DisjointColumnWeights.light Q (fun c ↦ (column x y L z c).card)).card : ℝ) := by
  have hret := DisjointColumnWeights.retained_card_real Q (fun c ↦ (column x y L z c).card)
  have hweight := actual_weight_real x y L z Q hx hy
  linarith

theorem component_size_budget {V : Type*} [Fintype V] (G : SimpleGraph V)
    (Q : Finset G.ConnectedComponent) :
    ∑ c ∈ Q, (componentVertices G c).card ≤ Fintype.card V := by
  classical
  calc
    _ = (Q.biUnion (componentVertices G)).card :=
      (card_biUnion (componentVertices_disjoint G Q)).symm
    _ ≤ _ := card_le_univ _

def smallComponents (x y L : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent) (M : ℕ) :
    Finset (largePrimeGraph x y L).ConnectedComponent :=
  Q.filter (fun c ↦ (componentVertices (largePrimeGraph x y L) c).card ≤ M)

theorem small_component_card_real (x y L : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (M : ℕ) : (Q.card : ℝ) - 2 * (L + 1 : ℕ) / (M + 1 : ℕ) ≤ ((smallComponents x y L Q M).card : ℝ) := by
  classical
  let big := Q.filter (fun c ↦ ¬(componentVertices (largePrimeGraph x y L) c).card ≤ M)
  have hbig : (M + 1) * big.card ≤ 2 * (L + 1) := by
    calc
      _ = ∑ _c ∈ big, (M + 1) := by
        simp only [sum_const, nsmul_eq_mul, Nat.cast_id]
        exact Nat.mul_comm _ _
      _ ≤ ∑ c ∈ big, (componentVertices (largePrimeGraph x y L) c).card := by
        apply sum_le_sum
        intro c hc
        have h := (mem_filter.mp hc).2
        omega
      _ ≤ ∑ c ∈ Q, (componentVertices (largePrimeGraph x y L) c).card :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ ↦ Nat.zero_le _)
      _ ≤ _ := by simpa only [LargePrimeGraphResolution.card_occurrence] using component_size_budget (largePrimeGraph x y L) Q
  have hpartition : ((smallComponents x y L Q M).card : ℝ) + big.card = Q.card := by
    exact_mod_cast card_filter_add_card_filter_not (s := Q)
      (fun c ↦ (componentVertices (largePrimeGraph x y L) c).card ≤ M)
  have hb : (M + 1 : ℕ) * (big.card : ℝ) ≤ 2 * (L + 1 : ℕ) := by exact_mod_cast hbig
  have hdiv : (big.card : ℝ) ≤ 2 * (L + 1 : ℕ) / (M + 1 : ℕ) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (M + 1 : ℕ))).mpr
    nlinarith
  linarith

theorem light_small_components_lower (x y L z : ℕ) (Q : Finset (largePrimeGraph x y L).ConnectedComponent)
    (M : ℕ) (hx : 0 < x) (hy : 0 < y) :
    (Q.card : ℝ) - 2 * (L + 1 : ℕ) / (M + 1 : ℕ) -
      (2 * (L + 1 : ℕ) * (∑ p ∈ mediumPrimes L z, 1 / (p : ℝ)) + 2 * (mediumPrimes L z).card) / 3 ≤
      ((DisjointColumnWeights.light (smallComponents x y L Q M)
        (fun c ↦ (column x y L z c).card)).card : ℝ) := by
  have hs := small_component_card_real x y L Q M
  have hl := light_components_lower x y L z (smallComponents x y L Q M) hx hy
  linarith

end PaperP1.MediumPrimeColumns
