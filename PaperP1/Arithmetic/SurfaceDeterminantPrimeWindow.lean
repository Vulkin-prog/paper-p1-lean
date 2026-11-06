module

public import PaperP1.Arithmetic.PrimeLogMertens
public import PaperP1.Arithmetic.SmallPrimeBudget

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SurfaceDeterminantPrimeWindow

open Finset DefectCounting

def primes (K X : ℕ) : Finset ℕ := smallPrimesUpTo X \ smallPrimesUpTo K

def mass (K X : ℕ) : ℝ := ∑ p ∈ primes K X, Real.log (p : ℝ) / p

def cost (K : ℕ) : ℝ := PrimeLogMertens.primePowerTotal + 1 + PrimeLogMertens.weightedPrimes K

theorem mem_primes (K X p : ℕ) : p ∈ primes K X ↔ p.Prime ∧ K < p ∧ p ≤ X := by
  simp only [primes, mem_sdiff, mem_smallPrimesUpTo]
  constructor
  · rintro ⟨⟨hp, hX⟩, hn⟩
    exact ⟨hp, lt_of_not_ge (fun hK ↦ hn ⟨hp, hK⟩), hX⟩
  · rintro ⟨hp, hK, hX⟩
    exact ⟨⟨hp, hX⟩, fun hh ↦ (not_le_of_gt hK) hh.2⟩

theorem full_mass_eq (X : ℕ) :
    (∑ p ∈ smallPrimesUpTo X, Real.log (p : ℝ) / p) = PrimeLogMertens.weightedPrimes X := by
  simp only [smallPrimesUpTo, Finset.sum_filter, PrimeLogMertens.weightedPrimes,
    PrimeLogMertens.coefficient]

theorem mass_difference (K X : ℕ) (hKX : K ≤ X) :
    mass K X = PrimeLogMertens.weightedPrimes X - PrimeLogMertens.weightedPrimes K := by
  have hsub : smallPrimesUpTo K ⊆ smallPrimesUpTo X := by
    intro p hp
    obtain ⟨hp, hK⟩ := mem_smallPrimesUpTo.mp hp
    exact mem_smallPrimesUpTo.mpr ⟨hp, hK.trans hKX⟩
  rw [mass, primes, Finset.sum_sdiff_eq_sub hsub, full_mass_eq, full_mass_eq]

theorem cost_nonneg (K : ℕ) : 0 ≤ cost K := by
  have hp := PrimeLogMertens.primePowerTotal_nonneg
  have hw : 0 ≤ PrimeLogMertens.weightedPrimes K := by
    apply Finset.sum_nonneg
    intro p _
    dsimp only [PrimeLogMertens.coefficient]
    split_ifs
    · exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
    · exact le_rfl
  dsimp only [cost]
  linarith

theorem mass_lower_bound (K X : ℕ) (hX : 1 ≤ X) (hKX : K ≤ X) :
    Real.log (X : ℝ) - cost K ≤ mass K X := by
  rw [mass_difference K X hKX]
  have hh := (PrimeLogMertens.natural_bounds X hX).1
  dsimp only [cost]
  linarith

theorem mass_upper_bound (K X : ℕ) (hX : 1 ≤ X) :
    mass K X ≤ Real.log (X : ℝ) + (Real.log 4 + 4) := by
  have hs : primes K X ⊆ smallPrimesUpTo X := Finset.sdiff_subset
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun p _ _ ↦ div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  rw [full_mass_eq X] at hh
  exact hh.trans (PrimeLogMertens.natural_bounds X hX).2

theorem theta_upper_bound (K X : ℕ) :
    (∑ p ∈ primes K X, Real.log (p : ℝ)) ≤ (X : ℝ) * Real.log 4 := by
  have hs : primes K X ⊆ smallPrimesUpTo X := Finset.sdiff_subset
  exact (Finset.sum_le_sum_of_subset_of_nonneg hs (fun p _ _ ↦ Real.log_natCast_nonneg p)).trans
    (SmallPrimeBudget.prime_log_sum_le X)

end PaperP1.SurfaceDeterminantPrimeWindow
