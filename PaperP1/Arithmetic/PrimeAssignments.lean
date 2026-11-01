module

public import PaperP1.Arithmetic.ModerateReceiverCost
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.Fintype.Prod

/-! # Assigning each actual prime once to a receiving window and offset -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeAssignments

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Code (P : Finset ℕ) (B : ℕ) := P → ι × Fin B

abbrev Group {P : Finset ℕ} {B : ℕ} (f : Code (ι := ι) P B) (i : ι) :=
  {p : P // (f p).1 = i}

def groupPrime {P : Finset ℕ} {B : ℕ} (f : Code (ι := ι) P B) (i : ι) (p : Group f i) : ℕ := p.val.val

def groupOffset {P : Finset ℕ} {B : ℕ} (f : Code (ι := ι) P B) (i : ι) (p : Group f i) : ℕ :=
  (f p.val).2.val

def groupModulus {P : Finset ℕ} {B : ℕ} (f : Code (ι := ι) P B) (i : ι) : ℕ :=
  PaperP1.ModerateReceiverCost.modulus (groupPrime f) i

omit [DecidableEq ι] in
theorem card_codes (P : Finset ℕ) (B : ℕ) :
    Fintype.card (Code (ι := ι) P B) = (Fintype.card ι * B) ^ P.card := by
  simp only [Code, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]

omit [Fintype ι] [DecidableEq ι] in
theorem groupPrime_prime {P : Finset ℕ} {B : ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (f : Code (ι := ι) P B) (i : ι) (p : Group f i) : Nat.Prime (groupPrime f i p) :=
  hP p.val.val p.val.property

omit [Fintype ι] [DecidableEq ι] in
theorem groupPrime_pairwise_coprime {P : Finset ℕ} {B : ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (f : Code (ι := ι) P B) (i : ι) :
    Pairwise (fun p q : Group f i ↦ Nat.Coprime (groupPrime f i p) (groupPrime f i q)) := by
  intro p q hpq
  apply (Nat.coprime_primes (groupPrime_prime hP f i p) (groupPrime_prime hP f i q)).mpr
  intro heq
  apply hpq
  apply Subtype.ext
  apply Subtype.ext
  exact heq

theorem product_groupModulus {P : Finset ℕ} {B : ℕ} (f : Code (ι := ι) P B) :
    (∏ i, groupModulus f i) = P.prod id := by
  change (∏ i, ∏ p : {p : P // (f p).1 = i}, p.val.val) = _
  rw [Fintype.prod_fiberwise]
  exact Finset.prod_coe_sort P id

omit [Fintype ι] in
theorem groupModulus_pairwise_coprime {P : Finset ℕ} {B : ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (f : Code (ι := ι) P B) : Pairwise (fun i j ↦ Nat.Coprime (groupModulus f i) (groupModulus f j)) := by
  intro i j hij
  apply Nat.coprime_fintype_prod_left_iff.mpr
  intro p
  apply Nat.coprime_fintype_prod_right_iff.mpr
  intro q
  apply (Nat.coprime_primes (groupPrime_prime hP f i p) (groupPrime_prime hP f j q)).mpr
  intro heq
  have hpq : p.val = q.val := Subtype.ext heq
  have hfi : (f p.val).1 = i := p.property
  have hfj : (f q.val).1 = j := q.property
  rw [hpq] at hfi
  exact hij (hfi.symm.trans hfj)

end PaperP1.PrimeAssignments
