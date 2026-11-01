module

public import PaperP1.Arithmetic.EvenPrimePatterns

/-! # First passage of a bounded prime product and its coprime allocations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeSubsetAllocations

open Finset

theorem first_passage (P : Finset ℕ) (X Y : ℝ) (hX : 1 ≤ X)
    (hP : ∀ p ∈ P, 1 ≤ p ∧ (p : ℝ) ≤ Y) (hprod : X < (P.prod id : ℕ)) :
    ∃ T : Finset ℕ, T ⊆ P ∧ X < (T.prod id : ℕ) ∧ (T.prod id : ℕ) ≤ X * Y := by
  classical
  induction P using Finset.induction_on with
  | empty => simp only [prod_empty, Nat.cast_one] at hprod; linarith
  | @insert p P hp ih =>
    by_cases hrest : X < (P.prod id : ℕ)
    · obtain ⟨T, hT, hlo, hhi⟩ := ih (fun q hq ↦ hP q (mem_insert_of_mem hq)) hrest
      exact ⟨T, hT.trans (subset_insert p P), hlo, hhi⟩
    · refine ⟨insert p P, Subset.rfl, hprod, ?_⟩
      rw [prod_insert hp, Nat.cast_mul]
      have hY : 0 ≤ Y := (Nat.cast_nonneg p).trans (hP p (mem_insert_self p P)).2
      calc
        (p : ℝ) * (P.prod id : ℕ) ≤ Y * X :=
          mul_le_mul (hP p (mem_insert_self p P)).2 (le_of_not_gt hrest) (Nat.cast_nonneg _) hY
        _ = _ := mul_comm _ _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def part (P : Finset ℕ) (f : ℕ → ι) (i : ι) : ℕ := (P.filter fun p ↦ f p = i).prod id

omit [Fintype ι] in
theorem part_pos (P : Finset ℕ) (f : ℕ → ι) (i : ι) (hP : ∀ p ∈ P, p.Prime) :
    0 < part P f i := by
  apply prod_pos
  intro p hp
  exact (hP p (mem_filter.mp hp).1).pos

theorem product_parts (P : Finset ℕ) (f : ℕ → ι) : ∏ i, part P f i = P.prod id := by
  unfold part
  rw [prod_fiberwise_eq_prod_filter]
  simp only [mem_univ, filter_true]

omit [Fintype ι] in
theorem prime_dvd_part (P : Finset ℕ) (f : ℕ → ι) (i : ι)
    (hP : ∀ p ∈ P, p.Prime) (p : ℕ) (hp : p.Prime) :
    p ∣ part P f i ↔ p ∈ P ∧ f p = i := by
  constructor
  · intro hdiv
    obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff id).mp hdiv
    have hdata := mem_filter.mp hq
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp (hP q hdata.1)).mp hpq
    exact heq ▸ hdata
  · intro h
    exact dvd_prod_of_mem id (mem_filter.mpr h)

omit [Fintype ι] in
theorem parts_coprime (P : Finset ℕ) (f : ℕ → ι) (hP : ∀ p ∈ P, p.Prime) :
    Pairwise fun i j ↦ Nat.Coprime (part P f i) (part P f j) := by
  intro i j hij
  apply Nat.coprime_of_dvd
  intro p hp hpi hpj
  have hi := (prime_dvd_part P f i hP p hp).mp hpi
  have hj := (prime_dvd_part P f j hP p hp).mp hpj
  exact hij (hi.2.symm.trans hj.2)

omit [Fintype ι] in
theorem part_dvd_value (P : Finset ℕ) (f : ℕ → ι) (i : ι) (n : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, f p = i → p ∣ n) : part P f i ∣ n := by
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (hP p (mem_filter.mp hp).1).prime
  · intro p hp
    exact hdiv p (mem_filter.mp hp).1 (mem_filter.mp hp).2

theorem exists_coprime_allocation [Nonempty ι] (P : Finset ℕ) (v : ι → ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hcover : ∀ p ∈ P, ∃ i, p ∣ v i) :
    ∃ G : ι → ℕ, (∀ i, 0 < G i ∧ G i ∣ v i) ∧
      Pairwise (fun i j ↦ Nat.Coprime (G i) (G j)) ∧ ∏ i, G i = P.prod id := by
  let f : ℕ → ι := fun p ↦ if hp : p ∈ P then Classical.choose (hcover p hp) else Classical.choice inferInstance
  have hf : ∀ p ∈ P, p ∣ v (f p) := by
    intro p hp
    simp only [f, dite_eq_left hp]
    exact Classical.choose_spec (hcover p hp)
  refine ⟨part P f, ?_, parts_coprime P f hP, product_parts P f⟩
  intro i
  refine ⟨part_pos P f i hP, part_dvd_value P f i (v i) hP ?_⟩
  intro p hp hpi
  simpa only [hpi] using hf p hp

end PaperP1.PrimeSubsetAllocations
