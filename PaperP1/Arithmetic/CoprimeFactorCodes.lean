module

public import PaperP1.Arithmetic.EvenPrimePatterns
public import Mathlib.Data.Fintype.Card

/-! # Counting actual coprime factorizations by assigning their prime factors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoprimeFactorCodes

open Finset

variable {κ : Type*} [Fintype κ]

theorem receiver_exists (m : ℕ) (D : κ → ℕ) (hprod : ∏ i, D i = m) (p : m.primeFactors) :
    ∃ i, p.val ∣ D i := by
  have hp := Nat.prime_of_mem_primeFactors p.property
  have hdiv : p.val ∣ ∏ i, D i := by rw [hprod]; exact Nat.dvd_of_mem_primeFactors p.property
  obtain ⟨i, _, hi⟩ := (hp.prime.dvd_finsetProd_iff D).mp hdiv
  exact ⟨i, hi⟩

def code (m : ℕ) (D : κ → ℕ) (hprod : ∏ i, D i = m) (p : m.primeFactors) : κ :=
  Classical.choose (receiver_exists m D hprod p)

theorem code_divides (m : ℕ) (D : κ → ℕ) (hprod : ∏ i, D i = m) (p : m.primeFactors) :
    p.val ∣ D (code m D hprod p) := Classical.choose_spec (receiver_exists m D hprod p)

theorem code_eq_of_divides (m : ℕ) (D : κ → ℕ) (hprod : ∏ i, D i = m)
    (hcop : Pairwise fun i j ↦ Nat.Coprime (D i) (D j))
    (p : m.primeFactors) (i : κ) (hi : p.val ∣ D i) : code m D hprod p = i := by
  by_contra hne
  have hg := Nat.dvd_gcd (code_divides m D hprod p) hi
  rw [(hcop hne).gcd_eq_one] at hg
  exact (Nat.prime_of_mem_primeFactors p.property).ne_one (Nat.dvd_one.mp hg)

theorem code_injective (m : ℕ) (D E : κ → ℕ)
    (hD : ∀ i, Squarefree (D i)) (hE : ∀ i, Squarefree (E i))
    (hprodD : ∏ i, D i = m) (hprodE : ∏ i, E i = m)
    (hcopD : Pairwise fun i j ↦ Nat.Coprime (D i) (D j))
    (hcopE : Pairwise fun i j ↦ Nat.Coprime (E i) (E j))
    (hcode : code m D hprodD = code m E hprodE) : D = E := by
  have transport : ∀ (D E : κ → ℕ) (hD : ∀ i, Squarefree (D i))
      (hprodD : ∏ i, D i = m) (hprodE : ∏ i, E i = m)
      (hcopD : Pairwise fun i j ↦ Nat.Coprime (D i) (D j)),
      code m D hprodD = code m E hprodE → ∀ i p, p.Prime → p ∣ D i → p ∣ E i := by
    intro D E hD hprodD hprodE hcopD hcode i p hp hpD
    have hm : m ≠ 0 := by
      rw [← hprodD]
      exact prod_ne_zero_iff.mpr (fun j _ ↦ (hD j).ne_zero)
    have hpm : p ∣ m := by
      rw [← hprodD]
      exact hpD.trans (dvd_prod_of_mem D (mem_univ i))
    let p' : m.primeFactors := ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpm, hm⟩⟩
    have hc := code_eq_of_divides m D hprodD hcopD p' i hpD
    have he := code_divides m E hprodE p'
    rw [← hcode, hc] at he
    exact he
  funext i
  apply (Nat.Squarefree.ext_iff (hD i) (hE i)).mpr
  intro p hp
  exact ⟨transport D E hD hprodD hprodE hcopD hcode i p hp,
    transport E D hE hprodE hprodD hcopE hcode.symm i p hp⟩

theorem card_families (m : ℕ) (V : Finset (κ → ℕ))
    (hsf : ∀ D ∈ V, ∀ i, Squarefree (D i)) (hprod : ∀ D ∈ V, ∏ i, D i = m)
    (hcop : ∀ D ∈ V, Pairwise fun i j ↦ Nat.Coprime (D i) (D j)) :
    V.card ≤ (Fintype.card κ) ^ m.primeFactors.card := by
  let f : V → (m.primeFactors → κ) := fun D ↦ code m D.val (hprod D.val D.property)
  have hf : Function.Injective f := by
    intro D E hDE
    apply Subtype.ext
    exact code_injective m D.val E.val (hsf D.val D.property) (hsf E.val E.property)
      (hprod D.val D.property) (hprod E.val E.property) (hcop D.val D.property) (hcop E.val E.property) hDE
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_fun] using hc

end PaperP1.CoprimeFactorCodes
