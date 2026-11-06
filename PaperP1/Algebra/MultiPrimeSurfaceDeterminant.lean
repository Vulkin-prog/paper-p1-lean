module

public import PaperP1.Algebra.NormalizedP3SurfaceDeterminant
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Int.Basic

/-! # Combining actual smooth surface congruences at distinct primes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MultiPrimeSurfaceDeterminant

open MvPolynomial Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem integer_dvd (S : Finset ℕ) (hprimes : ∀ p ∈ S, p.Prime) (L d : ℕ)
    (P : MvPolynomial (Fin 4) ℤ) (hhom : P.IsHomogeneous d) (a : ℕ → Fin 4 → ℤ)
    (ha : ∀ p ∈ S, a p 3 = 1) (hP : ∀ p ∈ S, (p : ℤ) ∣ eval (a p) P)
    (hgrad : ∀ p ∈ S, ∃ k, ¬(p : ℤ) ∣ eval (a p) (pderiv k P))
    (v : ι → Fin 4 → ℤ) (hvlast : ∀ j, v j 3 = 1)
    (hv : ∀ p ∈ S, ∀ j k, (p : ℤ) ∣ v j k - a p k)
    (hroots : ∀ j, eval (v j) P = 0) (F : ι → MvPolynomial (Fin 4) ℤ) :
    ((∏ p ∈ S, p : ℕ) : ℤ) ^ (L * Fintype.card ι - (L + 2).choose 3) ∣
      Matrix.det (fun i j ↦ eval (v j) (F i)) := by
  have hcop : (S : Set ℕ).Pairwise
      (fun p q ↦ IsCoprime ((p : ℤ) ^ (L * Fintype.card ι - (L + 2).choose 3))
        ((q : ℤ) ^ (L * Fintype.card ι - (L + 2).choose 3))) := by
    intro p hp q hq hpq
    have hn := (Nat.coprime_primes (hprimes p hp) (hprimes q hq)).mpr hpq
    have hz : IsCoprime (p : ℤ) (q : ℤ) := Int.isCoprime_iff_nat_coprime.mpr (by simpa using hn)
    exact hz.pow
  have hd : (∏ p ∈ S, (p : ℤ) ^ (L * Fintype.card ι - (L + 2).choose 3)) ∣
      Matrix.det (fun i j ↦ eval (v j) (F i)) := by
    apply Finset.prod_dvd_of_coprime hcop
    intro p hp
    exact NormalizedP3SurfaceDeterminant.integer_dvd p L d (hprimes p hp) P hhom
      (a p) (ha p hp) (hP p hp) (hgrad p hp) v hvlast (hv p hp) hroots F
  simpa only [Nat.cast_prod, Finset.prod_pow] using hd

theorem det_zero_of_small (S : Finset ℕ) (L : ℕ) (A : Matrix ι ι ℤ)
    (hdiv : ((∏ p ∈ S, p : ℕ) : ℤ) ^ (L * Fintype.card ι - (L + 2).choose 3) ∣ A.det)
    (hsmall : A.det.natAbs < (∏ p ∈ S, p) ^ (L * Fintype.card ι - (L + 2).choose 3)) : A.det = 0 := by
  by_contra hn
  have hb := Int.natAbs_le_of_dvd_ne_zero hdiv hn
  simp only [Int.natAbs_pow, Int.natAbs_natCast] at hb
  omega

end PaperP1.MultiPrimeSurfaceDeterminant
