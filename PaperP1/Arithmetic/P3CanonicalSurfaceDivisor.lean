module

public import PaperP1.Arithmetic.P3CanonicalSmoothResidues
public import PaperP1.Algebra.MultiPrimeClassifiedSurfaceDeterminant

/-! # The actual prime-specific determinant divisor computed from canonical residues of the original integer points -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3CanonicalSurfaceDivisor

open MvPolynomial Finset P3CanonicalSmoothResidues
open scoped Classical

def atPrime (p : ℕ) (P : MvPolynomial (Fin 4) ℤ) (v : Fin 4 → ℤ) : Option (Class p P) :=
  if hp : p.Prime then classification p hp.pos P v else none

variable {ι : Type*} [Fintype ι]

def population (p : ℕ) (P : MvPolynomial (Fin 4) ℤ) (v : ι → Fin 4 → ℤ) (c : Class p P) : ℕ :=
  Fintype.card {j // atPrime p P (v j) = some c}

def exponent (p : ℕ) (P : MvPolynomial (Fin 4) ℤ) (v : ι → Fin 4 → ℤ) (L : Class p P → ℕ) : ℕ :=
  ∑ c, (L c * population p P v c - (L c + 2).choose 3)

def divisor (S : Finset ℕ) (P : MvPolynomial (Fin 4) ℤ) (v : ι → Fin 4 → ℤ)
    (L : ∀ p, Class p P → ℕ) : ℕ := ∏ p ∈ S, p ^ exponent p P v (L p)

omit [Fintype ι] in
theorem atPrime_eq (p : ℕ) (hp : p.Prime) (P : MvPolynomial (Fin 4) ℤ) (v : Fin 4 → ℤ) :
    atPrime p P v = classification p hp.pos P v := by simp [atPrime, hp]

omit [Fintype ι] in
theorem unassigned_iff (p : ℕ) (hp : p.Prime) (P : MvPolynomial (Fin 4) ℤ)
    (v : Fin 4 → ℤ) (hv : v 3 = 1) (hroot : eval v P = 0) :
    atPrime p P v = none ↔ ∀ k, (p : ℤ) ∣ eval v (pderiv k P) := by
  rw [atPrime_eq p hp]
  exact classification_none_iff p hp.pos P v hv hroot

theorem total_population (p : ℕ) (P : MvPolynomial (Fin 4) ℤ) (v : ι → Fin 4 → ℤ) :
    (∑ c, population p P v c) + Fintype.card {j // atPrime p P (v j) = none} =
      Fintype.card ι := by
  have hh := Fintype.sum_fiberwise (fun j ↦ atPrime p P (v j)) (fun _ : ι ↦ (1 : ℕ))
  simp only [Finset.sum_const, card_univ, smul_eq_mul, mul_one] at hh
  rw [Fintype.sum_option] at hh
  simpa only [population, Nat.add_comm] using hh

variable [DecidableEq ι]

theorem integer_dvd (S : Finset ℕ) (hprimes : ∀ p ∈ S, p.Prime) (d : ℕ)
    (P : MvPolynomial (Fin 4) ℤ) (hhom : P.IsHomogeneous d)
    (v : ι → Fin 4 → ℤ) (hvlast : ∀ j, v j 3 = 1) (hroots : ∀ j, eval (v j) P = 0)
    (L : ∀ p, Class p P → ℕ) (F : ι → MvPolynomial (Fin 4) ℤ) :
    (divisor S P v L : ℤ) ∣ Matrix.det (fun i j ↦ eval (v j) (F i)) := by
  apply MultiPrimeClassifiedSurfaceDeterminant.integer_dvd (χ := fun p ↦ Class p P)
    S hprimes d P hhom (fun _ c ↦ representative c.val)
    (fun _ _ c ↦ representative_last c.val)
    (fun _ _ c ↦ c.property.1) (fun _ _ c ↦ c.property.2)
    (fun p j ↦ atPrime p P (v j)) L v hvlast
    (fun p hp j c hc ↦ classification_congruence p (hprimes p hp).pos P (v j) (hvlast j) c
      ((atPrime_eq p (hprimes p hp) P (v j)).symm.trans hc)) hroots F

theorem det_zero_of_small (S : Finset ℕ) (hprimes : ∀ p ∈ S, p.Prime) (d : ℕ)
    (P : MvPolynomial (Fin 4) ℤ) (hhom : P.IsHomogeneous d)
    (v : ι → Fin 4 → ℤ) (hvlast : ∀ j, v j 3 = 1) (hroots : ∀ j, eval (v j) P = 0)
    (L : ∀ p, Class p P → ℕ) (F : ι → MvPolynomial (Fin 4) ℤ)
    (hsmall : (Matrix.det (fun i j ↦ eval (v j) (F i))).natAbs < divisor S P v L) :
    Matrix.det (fun i j ↦ eval (v j) (F i)) = 0 := by
  exact MultiPrimeClassifiedSurfaceDeterminant.det_zero_of_small S
    (fun p ↦ exponent p P v (L p)) (fun i j ↦ eval (v j) (F i))
    (integer_dvd S hprimes d P hhom v hvlast hroots L F) hsmall

end PaperP1.P3CanonicalSurfaceDivisor
