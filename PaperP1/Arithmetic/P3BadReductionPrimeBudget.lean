module

public import PaperP1.Arithmetic.P3UniversalGoodReduction
public import PaperP1.Arithmetic.PrimeDivisorLogBudget
public import Mathlib.Data.Nat.PrimeFin

/-! # Actual bad geometric-reduction primes are finite and have a proved logarithmic budget -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3BadReductionPrimeBudget

open MvPolynomial Finset

def badPrimes (P : MvPolynomial (Fin 4) ℤ) : Set ℕ :=
  {p | ∃ hp : p.Prime, ¬ P3FiniteFieldClassEstimate.GeometricReduction p hp P}

theorem divides_certificate (P : MvPolynomial (Fin 4) ℤ) (z : ℤ)
    (hz : P3UniversalGoodReduction.Certificate P z) {p : ℕ} (hp : p ∈ badPrimes P) :
    (p : ℤ) ∣ z := by
  obtain ⟨hp, hbad⟩ := hp
  by_contra hnot
  exact hbad (P3UniversalGoodReduction.geometric_reduction P z hz p hp hnot)

theorem subset_prime_factors (P : MvPolynomial (Fin 4) ℤ) (z : ℤ) (hz : z ≠ 0)
    (hcert : P3UniversalGoodReduction.Certificate P z) :
    badPrimes P ⊆ (z.natAbs.primeFactors : Set ℕ) := by
  intro p hp
  exact Nat.mem_primeFactors.mpr ⟨hp.choose, Int.natCast_dvd.mp (divides_certificate P z hcert hp),
    Int.natAbs_ne_zero.mpr hz⟩

theorem finite (P : MvPolynomial (Fin 4) ℤ) (z : ℤ) (hz : z ≠ 0)
    (hcert : P3UniversalGoodReduction.Certificate P z) : (badPrimes P).Finite :=
  (z.natAbs.primeFactors.finite_toSet).subset (subset_prime_factors P z hz hcert)

theorem log_sum (P : MvPolynomial (Fin 4) ℤ) (z : ℤ) (hz : z ≠ 0)
    (hcert : P3UniversalGoodReduction.Certificate P z) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ badPrimes P) :
    (∑ p ∈ S, Real.log (p : ℝ)) ≤ Real.log (z.natAbs : ℝ) :=
  PrimeDivisorLogBudget.log_sum_le S (fun p hp ↦ (hS p hp).choose) z hz
    (fun p hp ↦ divides_certificate P z hcert (hS p hp))

theorem weighted_log_sum (P : MvPolynomial (Fin 4) ℤ) (z : ℤ) (hz : z ≠ 0)
    (hcert : P3UniversalGoodReduction.Certificate P z) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ badPrimes P) (K : ℝ) (hK : 0 < K)
    (hlarge : ∀ p ∈ S, K ≤ (p : ℝ)) :
    (∑ p ∈ S, Real.log (p : ℝ) / p) ≤ Real.log (z.natAbs : ℝ) / K :=
  PrimeDivisorLogBudget.weighted_log_sum_le S (fun p hp ↦ (hS p hp).choose) z hz
    (fun p hp ↦ divides_certificate P z hcert (hS p hp)) K hK hlarge

theorem log_height_bound (z : ℤ) (hz : z ≠ 0) (T A N : ℕ) (hT : 0 < T) (hA : 0 < A)
    (hbound : z.natAbs ≤ T * A ^ N) :
    Real.log (z.natAbs : ℝ) ≤ Real.log (T : ℝ) + (N : ℝ) * Real.log (A : ℝ) := by
  have hzpos : (0 : ℝ) < z.natAbs := by exact_mod_cast (Int.natAbs_pos.mpr hz)
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hbR : (z.natAbs : ℝ) ≤ ((T * A ^ N : ℕ) : ℝ) := by exact_mod_cast hbound
  have hh := Real.log_le_log hzpos hbR
  rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul hTR.ne' (pow_ne_zero N hAR.ne'), Real.log_pow] at hh
  exact hh

theorem uniform_log_budget (d : ℕ) :
    ∃ T N : ℕ, 0 < T ∧ ∀ A : ℕ, 0 < A → ∀ P : MvPolynomial (Fin 4) ℤ,
      P.IsHomogeneous d →
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) (map (Int.castRingHom ℚ) P)) →
      (∀ m, |P.coeff m| ≤ (A : ℤ)) →
      ∃ B : Finset ℕ, (∀ p : ℕ, p ∈ B ↔ p ∈ badPrimes P) ∧
        (∑ p ∈ B, Real.log (p : ℝ)) ≤ Real.log (T : ℝ) + (N : ℝ) * Real.log (A : ℝ) ∧
        ∀ K : ℝ, 0 < K →
          (∑ p ∈ B.filter (fun p : ℕ ↦ K ≤ (p : ℝ)), Real.log (p : ℝ) / p) ≤
            (Real.log (T : ℝ) + (N : ℝ) * Real.log (A : ℝ)) / K := by
  obtain ⟨T, N, hT, hcert⟩ := P3UniversalGoodReduction.bounded_certificate d
  refine ⟨T, N, hT, ?_⟩
  intro A hA P hP hgeom hcoef
  obtain ⟨z, hz, hbound, hgood⟩ := hcert A hA P hP hgeom hcoef
  let hf := finite P z hz hgood
  let B := hf.toFinset
  have hB (p : ℕ) : p ∈ B ↔ p ∈ badPrimes P := hf.mem_toFinset
  have hl := log_height_bound z hz T A N hT hA hbound
  refine ⟨B, hB, (log_sum P z hz hgood B (fun p hp ↦ (hB p).mp hp)).trans hl, ?_⟩
  intro K hK
  have hh := weighted_log_sum P z hz hgood (B.filter (fun p : ℕ ↦ K ≤ (p : ℝ)))
    (fun p hp ↦ (hB p).mp (mem_filter.mp hp).1) K hK (fun _ hp ↦ (mem_filter.mp hp).2)
  exact hh.trans (div_le_div_of_nonneg_right hl hK.le)

end PaperP1.P3BadReductionPrimeBudget
