module

public import PaperP1.Algebra.PartiallyClassifiedNormalizedSurfaceDeterminant
public import PaperP1.Algebra.MultiPrimeSurfaceDeterminant

/-! # Actual mixed-class surface divisors multiply at distinct primes, with prime-specific class populations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MultiPrimeClassifiedSurfaceDeterminant

open MvPolynomial Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {χ : ℕ → Type*} [∀ p, Fintype (χ p)] [∀ p, DecidableEq (χ p)]

theorem integer_dvd (S : Finset ℕ) (hprimes : ∀ p ∈ S, p.Prime) (d : ℕ)
    (P : MvPolynomial (Fin 4) ℤ) (hhom : P.IsHomogeneous d)
    (a : ∀ p, χ p → Fin 4 → ℤ) (ha : ∀ p ∈ S, ∀ c, a p c 3 = 1)
    (hP : ∀ p ∈ S, ∀ c, (p : ℤ) ∣ eval (a p c) P)
    (hgrad : ∀ p ∈ S, ∀ c, ∃ k, ¬(p : ℤ) ∣ eval (a p c) (pderiv k P))
    (b : ∀ p, ι → Option (χ p)) (L : ∀ p, χ p → ℕ)
    (v : ι → Fin 4 → ℤ) (hvlast : ∀ j, v j 3 = 1)
    (hv : ∀ p ∈ S, ∀ j c, b p j = some c → ∀ k, (p : ℤ) ∣ v j k - a p c k)
    (hroots : ∀ j, eval (v j) P = 0) (F : ι → MvPolynomial (Fin 4) ℤ) :
    ((∏ p ∈ S, p ^ (∑ c, (L p c * Fintype.card {j // b p j = some c} -
      (L p c + 2).choose 3)) : ℕ) : ℤ) ∣ Matrix.det (fun i j ↦ eval (v j) (F i)) := by
  let E : ℕ → ℕ := fun p ↦ ∑ c, (L p c * Fintype.card {j // b p j = some c} -
    (L p c + 2).choose 3)
  have hcop : (S : Set ℕ).Pairwise
      (fun p q ↦ IsCoprime ((p : ℤ) ^ E p) ((q : ℤ) ^ E q)) := by
    intro p hp q hq hpq
    have hn := (Nat.coprime_primes (hprimes p hp) (hprimes q hq)).mpr hpq
    have hz : IsCoprime (p : ℤ) (q : ℤ) := Int.isCoprime_iff_nat_coprime.mpr (by simpa using hn)
    exact hz.pow
  have hd : (∏ p ∈ S, (p : ℤ) ^ E p) ∣ Matrix.det (fun i j ↦ eval (v j) (F i)) := by
    apply Finset.prod_dvd_of_coprime hcop
    intro p hp
    exact PartiallyClassifiedNormalizedSurfaceDeterminant.integer_dvd p d (hprimes p hp) P hhom
      (a p) (ha p hp) (hP p hp) (hgrad p hp) (b p) (L p) v hvlast (hv p hp) hroots F
  simpa only [Nat.cast_prod, Nat.cast_pow] using hd

omit [∀ p, Fintype (χ p)] [∀ p, DecidableEq (χ p)] in
theorem det_zero_of_small (S : Finset ℕ) (E : ℕ → ℕ) (A : Matrix ι ι ℤ)
    (hdiv : ((∏ p ∈ S, p ^ E p : ℕ) : ℤ) ∣ A.det)
    (hsmall : A.det.natAbs < ∏ p ∈ S, p ^ E p) : A.det = 0 := by
  by_contra hn
  have hb := Int.natAbs_le_of_dvd_ne_zero hdiv hn
  simp only [Int.natAbs_natCast] at hb
  omega

end PaperP1.MultiPrimeClassifiedSurfaceDeterminant
