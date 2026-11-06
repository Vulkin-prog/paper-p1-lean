module

public import PaperP1.Arithmetic.P3UniversalGoodReduction
public import PaperP1.Arithmetic.CertificatePrimeWindow

/-! # An unconditional lower bound for the actual geometric-good-prime logarithmic mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3GeometricReductionPrimeWindow

open MvPolynomial Finset
open scoped Classical

def primes (K X : ℕ) (P : MvPolynomial (Fin 4) ℤ) : Finset ℕ :=
  (SurfaceDeterminantPrimeWindow.primes K X).filter
    (fun p ↦ ∃ hp : p.Prime, P3FiniteFieldClassEstimate.GeometricReduction p hp P)

def mass (K X : ℕ) (P : MvPolynomial (Fin 4) ℤ) : ℝ :=
  ∑ p ∈ primes K X P, Real.log (p : ℝ) / p

theorem mem_primes (K X p : ℕ) (P : MvPolynomial (Fin 4) ℤ) :
    p ∈ primes K X P ↔ ∃ hp : p.Prime, K < p ∧ p ≤ X ∧
      P3FiniteFieldClassEstimate.GeometricReduction p hp P := by
  rw [primes, mem_filter, SurfaceDeterminantPrimeWindow.mem_primes]
  constructor
  · rintro ⟨⟨hp, hK, hX⟩, ⟨_, hgeom⟩⟩
    exact ⟨hp, hK, hX, hgeom⟩
  · rintro ⟨hp, hK, hX, hgeom⟩
    exact ⟨⟨hp, hK, hX⟩, hp, hgeom⟩

theorem certificate_subset (K X : ℕ) (P : MvPolynomial (Fin 4) ℤ) (z : ℤ)
    (hcert : P3UniversalGoodReduction.Certificate P z) :
    CertificatePrimeWindow.primes K X z ⊆ primes K X P := by
  intro p hp
  obtain ⟨hp, hK, hX, hnot⟩ := (CertificatePrimeWindow.mem_primes K X p z).mp hp
  exact (mem_primes K X p P).mpr
    ⟨hp, hK, hX, P3UniversalGoodReduction.geometric_reduction P z hcert p hp hnot⟩

theorem certificate_mass_le (K X : ℕ) (P : MvPolynomial (Fin 4) ℤ) (z : ℤ)
    (hcert : P3UniversalGoodReduction.Certificate P z) :
    CertificatePrimeWindow.mass K X z ≤ mass K X P :=
  Finset.sum_le_sum_of_subset_of_nonneg (certificate_subset K X P z hcert)
    (fun p _ _ ↦ div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))

theorem mass_upper_bound (K X : ℕ) (P : MvPolynomial (Fin 4) ℤ) (hX : 1 ≤ X) :
    mass K X P ≤ Real.log (X : ℝ) + (Real.log 4 + 4) := by
  have hh : mass K X P ≤ SurfaceDeterminantPrimeWindow.mass K X :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p _ _ ↦ div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  exact hh.trans (SurfaceDeterminantPrimeWindow.mass_upper_bound K X hX)

theorem bounded_mass_lower_bound (K X : ℕ) (hK : 0 < K) (hX : 1 ≤ X) (hKX : K ≤ X)
    (P : MvPolynomial (Fin 4) ℤ) (z : ℤ) (hz : z ≠ 0)
    (hcert : P3UniversalGoodReduction.Certificate P z)
    (T A N : ℕ) (hT : 0 < T) (hA : 0 < A) (hbound : z.natAbs ≤ T * A ^ N) :
    Real.log (X : ℝ) - SurfaceDeterminantPrimeWindow.cost K -
      (Real.log (T : ℝ) + (N : ℝ) * Real.log (A : ℝ)) / K ≤ mass K X P :=
  (CertificatePrimeWindow.bounded_mass_lower_bound K X hK hX hKX z hz T A N hT
    (by omega) hbound).trans (certificate_mass_le K X P z hcert)

theorem uniform_mass_lower_bound (d : ℕ) :
    ∃ T N : ℕ, 0 < T ∧ ∀ A : ℕ, 0 < A → ∀ P : MvPolynomial (Fin 4) ℤ,
      P.IsHomogeneous d →
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) (map (Int.castRingHom ℚ) P)) →
      (∀ m, |P.coeff m| ≤ (A : ℤ)) →
      ∀ K X : ℕ, 0 < K → 1 ≤ X → K ≤ X →
        Real.log (X : ℝ) - SurfaceDeterminantPrimeWindow.cost K -
          (Real.log (T : ℝ) + (N : ℝ) * Real.log (A : ℝ)) / K ≤ mass K X P := by
  obtain ⟨T, N, hT, hcert⟩ := P3UniversalGoodReduction.bounded_certificate d
  refine ⟨T, N, hT, ?_⟩
  intro A hA P hP hgeom hcoef K X hK hX hKX
  obtain ⟨z, hz, hbound, hgood⟩ := hcert A hA P hP hgeom hcoef
  exact bounded_mass_lower_bound K X hK hX hKX P z hz hgood T A N hT hA hbound

end PaperP1.P3GeometricReductionPrimeWindow
