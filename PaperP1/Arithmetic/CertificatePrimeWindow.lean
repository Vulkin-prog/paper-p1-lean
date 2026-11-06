module

public import PaperP1.Arithmetic.SurfaceDeterminantPrimeWindow
public import PaperP1.Arithmetic.PrimeDivisorLogBudget

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CertificatePrimeWindow

open Finset

def primes (K X : ℕ) (z : ℤ) : Finset ℕ :=
  (SurfaceDeterminantPrimeWindow.primes K X).filter (fun p : ℕ ↦ ¬(p : ℤ) ∣ z)

def mass (K X : ℕ) (z : ℤ) : ℝ := ∑ p ∈ primes K X z, Real.log (p : ℝ) / p

theorem mem_primes (K X p : ℕ) (z : ℤ) :
    p ∈ primes K X z ↔ p.Prime ∧ K < p ∧ p ≤ X ∧ ¬(p : ℤ) ∣ z := by
  simp only [primes, mem_filter, SurfaceDeterminantPrimeWindow.mem_primes]
  tauto

theorem mass_split (K X : ℕ) (z : ℤ) :
    mass K X z +
      (∑ p ∈ (SurfaceDeterminantPrimeWindow.primes K X).filter (fun p : ℕ ↦ (p : ℤ) ∣ z),
        Real.log (p : ℝ) / p) = SurfaceDeterminantPrimeWindow.mass K X := by
  have hh := Finset.sum_filter_add_sum_filter_not (SurfaceDeterminantPrimeWindow.primes K X)
    (fun p : ℕ ↦ ¬(p : ℤ) ∣ z) (fun p ↦ Real.log (p : ℝ) / p)
  simpa only [mass, primes, not_not, SurfaceDeterminantPrimeWindow.mass] using hh

theorem mass_lower_bound (K X : ℕ) (hK : 0 < K) (hX : 1 ≤ X) (hKX : K ≤ X)
    (z : ℤ) (hz : z ≠ 0) :
    Real.log (X : ℝ) - SurfaceDeterminantPrimeWindow.cost K - Real.log (z.natAbs : ℝ) / K ≤
      mass K X z := by
  let B : Finset ℕ := (SurfaceDeterminantPrimeWindow.primes K X).filter (fun p : ℕ ↦ (p : ℤ) ∣ z)
  have hprime : ∀ p ∈ B, p.Prime := fun p hp ↦
    (SurfaceDeterminantPrimeWindow.mem_primes K X p).mp (mem_filter.mp hp).1 |>.1
  have hdiv : ∀ p ∈ B, (p : ℤ) ∣ z := fun _ hp ↦ (mem_filter.mp hp).2
  have hlarge : ∀ p ∈ B, (K : ℝ) ≤ p := by
    intro p hp
    have hh := ((SurfaceDeterminantPrimeWindow.mem_primes K X p).mp (mem_filter.mp hp).1).2.1
    exact_mod_cast hh.le
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hb := PrimeDivisorLogBudget.weighted_log_sum_le B hprime z hz hdiv K hKR hlarge
  have hs := mass_split K X z
  have hl := SurfaceDeterminantPrimeWindow.mass_lower_bound K X hX hKX
  change (∑ p ∈ B, Real.log (p : ℝ) / p) ≤ Real.log (z.natAbs : ℝ) / K at hb
  linarith

theorem bounded_mass_lower_bound (K X : ℕ) (hK : 0 < K) (hX : 1 ≤ X) (hKX : K ≤ X)
    (z : ℤ) (hz : z ≠ 0) (T H c : ℕ) (hT : 0 < T) (hH : 1 ≤ H)
    (hbound : z.natAbs ≤ T * H ^ c) :
    Real.log (X : ℝ) - SurfaceDeterminantPrimeWindow.cost K -
      (Real.log (T : ℝ) + (c : ℝ) * Real.log (H : ℝ)) / K ≤ mass K X z := by
  have hzpos : (0 : ℝ) < z.natAbs := by exact_mod_cast (Int.natAbs_pos.mpr hz)
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hHR : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hbR : (z.natAbs : ℝ) ≤ ((T * H ^ c : ℕ) : ℝ) := by exact_mod_cast hbound
  have hl := Real.log_le_log hzpos hbR
  rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul hTR.ne' (pow_ne_zero c hHR.ne'), Real.log_pow] at hl
  have hKR : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hd := div_le_div_of_nonneg_right hl hKR
  linarith [mass_lower_bound K X hK hX hKX z hz]

theorem theta_upper_bound (K X : ℕ) (z : ℤ) :
    (∑ p ∈ primes K X z, Real.log (p : ℝ)) ≤ (X : ℝ) * Real.log 4 := by
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun p _ _ ↦ Real.log_natCast_nonneg p)).trans
    (SurfaceDeterminantPrimeWindow.theta_upper_bound K X)

end PaperP1.CertificatePrimeWindow
