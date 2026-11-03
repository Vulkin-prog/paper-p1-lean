module

public import PaperP1.Arithmetic.FiniteRungeIndependence
public import PaperP1.Asymptotics.CriticalPolynomialScale

/-! # Every fixed-size actual selection in a polynomial-logarithmic interval is uniformly even-independent -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalFiniteRungeIndependence

open Finset

theorem uniform_independent (C : ℝ) (K D J : ℕ) (hD : 1 ≤ D) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ U R : ℕ, N ≤ 2 * U → 1 ≤ R → R ≤ D * (L + 1) ^ J →
      ∀ S : Finset ℕ, S.card ≤ K → (∀ n ∈ S, U ≤ n ∧ n ≤ U + R) →
        EvenIndependentValues.Independent S := by
  obtain ⟨Nr, hr⟩ := CriticalPolynomialScale.polynomial_lt_scale C (4 * D) (by positivity) J
  obtain ⟨Ng, hg⟩ := CriticalPolynomialScale.polynomial_lt_scale C (4 * (64 * D) ^ (2 * K))
    (by positivity) (J * (2 * K))
  refine ⟨max 3 (max Nr Ng), by omega, ?_⟩
  intro N hN L hband U R hNU hR hwidth S hcard hS
  have hrad : 4 * (D * (L + 1) ^ J) < N := by
    have h := hr N (by omega) L hband
    have h' : (4 : ℝ) * ((D : ℝ) * (L + 1 : ℕ) ^ J) < N := by simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using h
    exact_mod_cast h'
  have hbig : 4 * ((64 * D) ^ (2 * K) * (L + 1) ^ (J * (2 * K))) < N := by
    have h := hg N (by omega) L hband
    have h' : (4 : ℝ) * (((64 * D : ℕ) : ℝ) ^ (2 * K) *
        ((L + 1 : ℕ) : ℝ) ^ (J * (2 * K))) < N := by
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using h
    exact_mod_cast h'
  have hpow : (64 * R) ^ (2 * K) ≤ (64 * D) ^ (2 * K) * (L + 1) ^ (J * (2 * K)) := by
    calc
      _ ≤ (64 * (D * (L + 1) ^ J)) ^ (2 * K) := Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hwidth) _
      _ = _ := by rw [← mul_assoc, mul_pow, ← pow_mul]
  apply FiniteRungeIndependence.independent_of_growth (t := K) (by omega)
    (fun n hn ↦ (hS n hn).1) (fun n hn ↦ (hS n hn).2) hR
  · have h4 := Nat.mul_le_mul_left 4 hwidth
    omega
  · omega

end PaperP1.CriticalFiniteRungeIndependence
