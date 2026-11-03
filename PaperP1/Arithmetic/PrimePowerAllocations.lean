module

public import PaperP1.Arithmetic.PrimeSubsetAllocations
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Algebra.GCDMonoid.FinsetLemmas

/-! # Coprime allocation of complete prime powers of an actual lcm divisor -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimePowerAllocations

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def part (m : ℕ) (f : ℕ → ι) (i : ι) : ℕ :=
  (m.primeFactors.filter fun p ↦ f p = i).prod fun p ↦ p ^ m.factorization p

omit [Fintype ι] in
theorem part_pos (m : ℕ) (f : ℕ → ι) (i : ι) : 0 < part m f i := by
  apply prod_pos
  intro p hp
  exact pow_pos (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos _

theorem product_parts (m : ℕ) (hm : 0 < m) (f : ℕ → ι) : ∏ i, part m f i = m := by
  unfold part
  rw [prod_fiberwise_eq_prod_filter]
  simpa only [mem_univ, filter_true] using (Nat.prod_primeFactors_pow_factorization hm.ne').symm

omit [Fintype ι] in
theorem parts_coprime (m : ℕ) (f : ℕ → ι) : Pairwise fun i j ↦ Nat.Coprime (part m f i) (part m f j) := by
  intro i j hij
  unfold part
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro q hq
  have hpi := mem_filter.mp hp
  have hqj := mem_filter.mp hq
  have hpq : p ≠ q := by
    intro heq
    exact hij (hpi.2.symm.trans (heq ▸ hqj.2))
  exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hpi.1)
    (Nat.prime_of_mem_primeFactors hqj.1)).mpr hpq).pow _ _

omit [Fintype ι] in
theorem part_dvd (m : ℕ) (f : ℕ → ι) (i : ι) (v : ℕ)
    (hdiv : ∀ p ∈ m.primeFactors, f p = i → p ^ m.factorization p ∣ v) : part m f i ∣ v := by
  apply Finset.prod_dvd_of_isRelPrime
  · intro p hp q hq hpq
    have hc := ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)
      (Nat.prime_of_mem_primeFactors (mem_filter.mp hq).1)).mpr hpq).pow (m.factorization p) (m.factorization q)
    exact Nat.coprime_iff_isRelPrime.mp hc
  · intro p hp
    exact hdiv p (mem_filter.mp hp).1 (mem_filter.mp hp).2

theorem exists_allocation [Nonempty ι] (m : ℕ) (hm : 0 < m) (v : ι → ℕ)
    (hcover : ∀ p ∈ m.primeFactors, ∃ i, p ^ m.factorization p ∣ v i) :
    ∃ G : ι → ℕ, (∀ i, 0 < G i ∧ G i ∣ v i) ∧
      Pairwise (fun i j ↦ Nat.Coprime (G i) (G j)) ∧ ∏ i, G i = m := by
  let f : ℕ → ι := fun p ↦ if hp : p ∈ m.primeFactors then Classical.choose (hcover p hp) else Classical.choice inferInstance
  have hf : ∀ p ∈ m.primeFactors, p ^ m.factorization p ∣ v (f p) := by
    intro p hp
    simp only [f, dite_eq_left hp]
    exact Classical.choose_spec (hcover p hp)
  refine ⟨part m f, ?_, parts_coprime m f, product_parts m hm f⟩
  intro i
  exact ⟨part_pos m f i, part_dvd m f i (v i) (fun p hp hpi ↦ by simpa only [hpi] using hf p hp)⟩

omit [Fintype ι] in
theorem prime_power_receiver (S : Finset ι) (v : ι → ℕ) (p e : ℕ)
    (hp : p.Prime) (he : 0 < e) (hv : ∀ i ∈ S, 0 < v i) (hdiv : p ^ e ∣ S.lcm v) :
    ∃ i ∈ S, p ^ e ∣ v i := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have hbad : p ∣ 1 := (dvd_pow_self p he.ne').trans (by simpa only [lcm_empty] using hdiv)
    exact False.elim (hp.not_dvd_one hbad)
  | @insert i S hi ih =>
    have hi0 : v i ≠ 0 := (hv i (mem_insert_self i S)).ne'
    have hvS : ∀ j ∈ S, 0 < v j := fun j hj ↦ hv j (mem_insert_of_mem hj)
    have hS0 : S.lcm v ≠ 0 := Finset.lcm_ne_zero_iff.mpr (fun j hj ↦ (hvS j hj).ne')
    rw [lcm_insert, lcm_eq_nat_lcm] at hdiv
    have heq := (hp.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero hi0 hS0)).mp hdiv
    rw [Nat.factorization_lcm hi0 hS0, Finsupp.sup_apply] at heq
    rcases le_max_iff.mp heq with hleft | hright
    · exact ⟨i, mem_insert_self _ _, (hp.pow_dvd_iff_le_factorization hi0).mpr hleft⟩
    · obtain ⟨j, hj, hpow⟩ := ih hvS ((hp.pow_dvd_iff_le_factorization hS0).mpr hright)
      exact ⟨j, mem_insert_of_mem hj, hpow⟩

theorem exists_allocation_of_dvd_lcm [Nonempty ι] (m : ℕ) (hm : 0 < m) (v : ι → ℕ)
    (hv : ∀ i, 0 < v i) (hdiv : m ∣ univ.lcm v) :
    ∃ G : ι → ℕ, (∀ i, 0 < G i ∧ G i ∣ v i) ∧
      Pairwise (fun i j ↦ Nat.Coprime (G i) (G j)) ∧ ∏ i, G i = m := by
  apply exists_allocation m hm v
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpdvd := Nat.dvd_of_mem_primeFactors hp
  have he : 0 < m.factorization p := hprime.factorization_pos_of_dvd hm.ne' hpdvd
  have hpow : p ^ m.factorization p ∣ m := (hprime.pow_dvd_iff_le_factorization hm.ne').mpr le_rfl
  obtain ⟨i, _hi, hd⟩ := prime_power_receiver univ v p (m.factorization p) hprime he
    (fun i _ ↦ hv i) (hpow.trans hdiv)
  exact ⟨i, hd⟩

end PaperP1.PrimePowerAllocations
