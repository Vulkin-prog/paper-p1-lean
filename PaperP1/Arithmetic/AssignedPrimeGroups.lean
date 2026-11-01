module

public import PaperP1.Arithmetic.SquarefreeKernelProducts
public import Mathlib.Data.Nat.GCD.BigOperators

/-! # Actual disjoint prime groups assigned to physical certificates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AssignedPrimeGroups

open Finset

variable {κ : Type*} [DecidableEq κ]

def primes (P : Finset ℕ) (assign : ℕ → κ) (a : κ) : Finset ℕ := P.filter fun p ↦ assign p = a

def group (P : Finset ℕ) (assign : ℕ → κ) (a : κ) : ℕ := (primes P assign a).prod id

def groups (P : Finset ℕ) (assign : ℕ → κ) : Finset κ := P.image assign

theorem mem_primes (P : Finset ℕ) (assign : ℕ → κ) (a : κ) (p : ℕ) :
    p ∈ primes P assign a ↔ p ∈ P ∧ assign p = a := mem_filter

theorem group_pos (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (assign : ℕ → κ) (a : κ) :
    0 < group P assign a :=
  prod_pos (fun p hp ↦ (hP p ((mem_primes P assign a p).mp hp).1).pos)

theorem assigned_prime_dvd (P : Finset ℕ) (assign : ℕ → κ) {p : ℕ} (hp : p ∈ P) :
    p ∣ group P assign (assign p) :=
  dvd_prod_of_mem id ((mem_primes P assign (assign p) p).mpr ⟨hp, rfl⟩)

theorem group_gt_one (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (assign : ℕ → κ)
    {a : κ} (ha : a ∈ groups P assign) : 1 < group P assign a := by
  obtain ⟨p, hp, rfl⟩ := mem_image.mp ha
  exact (hP p hp).one_lt.trans_le (Nat.le_of_dvd (group_pos P hP assign _) (assigned_prime_dvd P assign hp))

theorem group_coprime (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (assign : ℕ → κ)
    {a b : κ} (hab : a ≠ b) : Nat.Coprime (group P assign a) (group P assign b) := by
  unfold group
  rw [Nat.coprime_prod_left_iff]
  intro p hp
  rw [Nat.coprime_prod_right_iff]
  intro q hq
  obtain ⟨hpP, hpa⟩ := (mem_primes P assign a p).mp hp
  obtain ⟨hqP, hqb⟩ := (mem_primes P assign b q).mp hq
  apply (Nat.coprime_primes (hP p hpP) (hP q hqP)).mpr
  intro hpq
  exact hab (hpa.symm.trans ((congrArg assign hpq).trans hqb))

theorem group_squarefree (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (assign : ℕ → κ) (a : κ) :
    Squarefree (group P assign a) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hP p ((mem_primes P assign a p).mp hp).1)
        (hP q ((mem_primes P assign a q).mp hq).1)).mpr hpq)
  · intro p hp
    exact (hP p ((mem_primes P assign a p).mp hp).1).squarefree

theorem group_dvd (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (assign : ℕ → κ) (a : κ) (n : ℕ)
    (hdiv : ∀ p ∈ primes P assign a, p ∣ n) : group P assign a ∣ n := by
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (hP p ((mem_primes P assign a p).mp hp).1).prime
  · exact hdiv

theorem covered_prime_product_dvd (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (assign : ℕ → κ) (Q : Finset ℕ) (G : Finset κ) (hQP : Q ⊆ P)
    (hcover : ∀ p ∈ Q, assign p ∈ G) : Q.prod id ∣ ∏ a ∈ G, group P assign a := by
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (hP p (hQP hp)).prime
  · intro p hp
    exact (assigned_prime_dvd P assign (hQP hp)).trans
      (dvd_prod_of_mem (fun a ↦ group P assign a) (hcover p hp))

theorem covered_prime_product_le (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (assign : ℕ → κ) (Q : Finset ℕ) (G : Finset κ) (hQP : Q ⊆ P)
    (hcover : ∀ p ∈ Q, assign p ∈ G) : Q.prod id ≤ ∏ a ∈ G, group P assign a :=
  Nat.le_of_dvd (prod_pos (fun a _ ↦ group_pos P hP assign a))
    (covered_prime_product_dvd P hP assign Q G hQP hcover)

end PaperP1.AssignedPrimeGroups
