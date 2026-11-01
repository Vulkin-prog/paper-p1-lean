module

public import PaperP1.Arithmetic.SquarefreeKernelProducts
public import Mathlib.Data.Fintype.Powerset

/-! # Canonical prime occurrence patterns of squarefree tuples -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EvenPrimePatterns

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pool (q : ι → ℕ) : Finset ℕ := univ.biUnion fun i ↦ (q i).primeFactors

def occurrence (q : ι → ℕ) (p : ℕ) : Finset ι := univ.filter fun i ↦ p ∣ q i

def support (q : ι → ℕ) (S : Finset ι) : Finset ℕ :=
  (pool q).filter fun p ↦ occurrence q p = S

def part (q : ι → ℕ) (S : Finset ι) : ℕ := (support q S).prod id

def patterns : Finset (Finset ι) := univ.filter fun S ↦ 2 ≤ S.card ∧ Even S.card

omit [DecidableEq ι] in
theorem mem_occurrence (q : ι → ℕ) (p : ℕ) (i : ι) :
    i ∈ occurrence q p ↔ p ∣ q i := by simp [occurrence]

omit [DecidableEq ι] in
theorem prime_of_mem_pool (q : ι → ℕ) (p : ℕ) (hp : p ∈ pool q) : p.Prime := by
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp hp
  exact Nat.prime_of_mem_primeFactors hi

omit [DecidableEq ι] in
theorem occurrence_nonempty (q : ι → ℕ) (p : ℕ) (hp : p ∈ pool q) :
    (occurrence q p).Nonempty := by
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp hp
  exact ⟨i, (mem_occurrence q p i).mpr (Nat.dvd_of_mem_primeFactors hi)⟩

theorem part_pos (q : ι → ℕ) (S : Finset ι) : 0 < part q S := by
  apply prod_pos
  intro p hp
  exact (prime_of_mem_pool q p (mem_filter.mp hp).1).pos

theorem part_squarefree (q : ι → ℕ) (S : Finset ι) : Squarefree (part q S) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp r hr hpr
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes
      (prime_of_mem_pool q p (mem_filter.mp hp).1)
      (prime_of_mem_pool q r (mem_filter.mp hr).1)).mpr hpr)
  · intro p hp
    exact (prime_of_mem_pool q p (mem_filter.mp hp).1).squarefree

theorem prime_dvd_part_iff (q : ι → ℕ) (S : Finset ι) (p : ℕ) (hp : p.Prime) :
    p ∣ part q S ↔ p ∈ support q S := by
  constructor
  · intro hd
    obtain ⟨r, hr, hpr⟩ := (hp.prime.dvd_finsetProd_iff id).mp hd
    have heq : p = r := (Nat.prime_dvd_prime_iff_eq hp
      (prime_of_mem_pool q r (mem_filter.mp hr).1)).mp hpr
    exact heq ▸ hr
  · exact fun h ↦ dvd_prod_of_mem id h

theorem part_coprime (q : ι → ℕ) (S T : Finset ι) (hST : S ≠ T) :
    Nat.Coprime (part q S) (part q T) := by
  apply Nat.coprime_of_dvd
  intro p hp hpS hpT
  have hs := (mem_filter.mp ((prime_dvd_part_iff q S p hp).mp hpS)).2
  have ht := (mem_filter.mp ((prime_dvd_part_iff q T p hp).mp hpT)).2
  exact hST (hs.symm.trans ht)

theorem part_dvd_coordinate (q : ι → ℕ) (S : Finset ι) (i : ι) (hi : i ∈ S) :
    part q S ∣ q i := by
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (prime_of_mem_pool q p (mem_filter.mp hp).1).prime
  · intro p hp
    have hocc := (mem_filter.mp hp).2
    exact (mem_occurrence q p i).mp (hocc.symm ▸ hi)

theorem reconstruction (q : ι → ℕ) (hq : ∀ i, Squarefree (q i)) (i : ι) :
    (∏ S ∈ univ.filter (fun S : Finset ι ↦ i ∈ S), part q S) = q i := by
  have hfilter : (pool q).filter (fun p ↦ occurrence q p ∈
      univ.filter (fun S : Finset ι ↦ i ∈ S)) = (q i).primeFactors := by
    ext p
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hp, hi⟩
      exact Nat.mem_primeFactors.mpr ⟨prime_of_mem_pool q p hp,
        (mem_occurrence q p i).mp hi, (hq i).ne_zero⟩
    · intro hp
      exact ⟨mem_biUnion.mpr ⟨i, mem_univ i, hp⟩,
        (mem_occurrence q p i).mpr (Nat.dvd_of_mem_primeFactors hp)⟩
  unfold part support
  rw [prod_fiberwise_eq_prod_filter, hfilter]
  exact Nat.prod_primeFactors_of_squarefree (hq i)

omit [DecidableEq ι] in
theorem factorization_eq_occurrence_card (q : ι → ℕ) (hq : ∀ i, Squarefree (q i))
    (p : ℕ) (hp : p.Prime) :
    (∏ i, q i).factorization p = (occurrence q p).card := by
  rw [Nat.factorization_prod_apply (fun i _ ↦ (hq i).ne_zero)]
  simp only [occurrence, card_eq_sum_ones, sum_filter]
  apply sum_congr rfl
  intro i _
  by_cases hd : p ∣ q i
  · simp only [hd, ite_true, Nat.factorization_eq_one_of_squarefree (hq i) hp hd]
  · simp only [hd, ite_false, Nat.factorization_eq_zero_of_not_dvd hd]

omit [DecidableEq ι] in
theorem occurrence_even (q : ι → ℕ) (hq : ∀ i, Squarefree (q i))
    (hsq : IsSquare (∏ i, q i)) (p : ℕ) (hp : p.Prime) :
    Even (occurrence q p).card := by
  obtain ⟨r, hr⟩ := hsq
  rw [← factorization_eq_occurrence_card q hq p hp, hr,
    ← pow_two, Nat.factorization_pow, Finsupp.smul_apply]
  exact ⟨r.factorization p, by simp [two_mul]⟩

omit [DecidableEq ι] in
theorem occurrence_mem_patterns (q : ι → ℕ) (hq : ∀ i, Squarefree (q i))
    (hsq : IsSquare (∏ i, q i)) (p : ℕ) (hp : p ∈ pool q) :
    occurrence q p ∈ patterns := by
  have hnonempty := (occurrence_nonempty q p hp).card_pos
  have heven := occurrence_even q hq hsq p (prime_of_mem_pool q p hp)
  have htwo : 2 ≤ (occurrence q p).card := by
    obtain ⟨k, hk⟩ := heven
    omega
  exact mem_filter.mpr ⟨mem_univ _, htwo, heven⟩

theorem part_eq_one_outside_patterns (q : ι → ℕ) (hq : ∀ i, Squarefree (q i))
    (hsq : IsSquare (∏ i, q i)) (S : Finset ι) (hS : S ∉ patterns) :
    part q S = 1 := by
  apply prod_eq_one
  intro p hp
  obtain ⟨hppool, hocc⟩ := mem_filter.mp hp
  exact False.elim (hS (hocc ▸ occurrence_mem_patterns q hq hsq p hppool))

theorem even_reconstruction (q : ι → ℕ) (hq : ∀ i, Squarefree (q i))
    (hsq : IsSquare (∏ i, q i)) (i : ι) :
    (∏ S ∈ patterns.filter (fun S ↦ i ∈ S), part q S) = q i := by
  calc
    _ = ∏ S ∈ univ.filter (fun S : Finset ι ↦ i ∈ S), part q S := by
      apply prod_subset
      · intro S hS
        exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hS).2⟩
      · intro S hS hnot
        apply part_eq_one_outside_patterns q hq hsq S
        intro hSp
        exact hnot (mem_filter.mpr ⟨hSp, (mem_filter.mp hS).2⟩)
    _ = q i := reconstruction q hq i

theorem candidate_occurrence (q : ι → ℕ) (D : Finset ι → ℕ)
    (hcop : ∀ S ∈ patterns, ∀ T ∈ patterns, S ≠ T → Nat.Coprime (D S) (D T))
    (hrec : ∀ i, (∏ S ∈ patterns.filter (fun S ↦ i ∈ S), D S) = q i)
    (S : Finset ι) (hS : S ∈ patterns) (p : ℕ) (hp : p.Prime) (hpd : p ∣ D S) :
    occurrence q p = S := by
  ext i
  rw [mem_occurrence]
  constructor
  · intro hpi
    rw [← hrec i] at hpi
    obtain ⟨T, hT, hpT⟩ := (hp.prime.dvd_finsetProd_iff D).mp hpi
    obtain ⟨hTp, hiT⟩ := mem_filter.mp hT
    have hST : S = T := by
      by_contra hne
      have hg := Nat.dvd_gcd hpd hpT
      rw [(hcop S hS T hTp hne).gcd_eq_one] at hg
      exact hp.ne_one (Nat.dvd_one.mp hg)
    exact hST ▸ hiT
  · intro hiS
    rw [← hrec i]
    exact hpd.trans (dvd_prod_of_mem D (mem_filter.mpr ⟨hS, hiS⟩))

theorem unique_parts (q : ι → ℕ) (hq : ∀ i, Squarefree (q i))
    (D : Finset ι → ℕ) (hD : ∀ S ∈ patterns, Squarefree (D S))
    (hcop : ∀ S ∈ patterns, ∀ T ∈ patterns, S ≠ T → Nat.Coprime (D S) (D T))
    (hrec : ∀ i, (∏ S ∈ patterns.filter (fun S ↦ i ∈ S), D S) = q i)
    (S : Finset ι) (hS : S ∈ patterns) : D S = part q S := by
  apply (Nat.Squarefree.ext_iff (hD S hS) (part_squarefree q S)).mpr
  intro p hp
  rw [prime_dvd_part_iff q S p hp]
  have hSne : S.Nonempty := card_pos.mp (by
    have htwo := (mem_filter.mp hS).2.1
    omega)
  constructor
  · intro hpD
    have hocc := candidate_occurrence q D hcop hrec S hS p hp hpD
    obtain ⟨i, hi⟩ := hSne
    have hpi : p ∣ q i := (mem_occurrence q p i).mp (hocc.symm ▸ hi)
    have hpool : p ∈ pool q := mem_biUnion.mpr ⟨i, mem_univ _,
      Nat.mem_primeFactors.mpr ⟨hp, hpi, (hq i).ne_zero⟩⟩
    exact mem_filter.mpr ⟨hpool, hocc⟩
  · intro hpc
    have hocc := (mem_filter.mp hpc).2
    obtain ⟨i, hi⟩ := hSne
    have hpi : p ∣ q i := (mem_occurrence q p i).mp (hocc.symm ▸ hi)
    rw [← hrec i] at hpi
    obtain ⟨T, hT, hpT⟩ := (hp.prime.dvd_finsetProd_iff D).mp hpi
    have hTp := (mem_filter.mp hT).1
    have hST : S = T := hocc.symm.trans (candidate_occurrence q D hcop hrec T hTp p hp hpT)
    exact hST.symm ▸ hpT

end PaperP1.EvenPrimePatterns
