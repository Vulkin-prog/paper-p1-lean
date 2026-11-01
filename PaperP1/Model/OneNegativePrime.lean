module

public import PaperP1.Model.FiniteRademacher
public import Mathlib.Data.Nat.Factorization.Basic

/-! # One negative prime forces exact positive runs of length q-1 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OneNegativePrime

open Finset PaperP1.Arithmetic PaperP1.Model

def sample {M : ℕ} (q : PrimeUpTo M) : SampleSpace M := Pi.single q 1

theorem valueBit_sample {M : ℕ} (q : PrimeUpTo M) (n : ℕ) : valueBit (sample q) n = parityVec n q.val.val := by
  classical
  simp [valueBit, sample, Pi.single_apply]

theorem parity_zero_of_not_dvd {q n : ℕ} (hqn : ¬q ∣ n) : parityVec n q = 0 := by
  simp only [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd hqn, Nat.cast_zero]

theorem parity_simple_multiple {q u : ℕ} (hq : Nat.Prime q) (hu : ¬q ∣ u) : parityVec (q * u) q = 1 := by
  have hu0 : u ≠ 0 := by intro h; exact hu (h ▸ dvd_zero q)
  rw [parityVec_mul hq.ne_zero hu0]
  simp only [Finsupp.add_apply, parity_zero_of_not_dvd hu, add_zero, parityVec_apply,
    hq.factorization_self, Nat.cast_one]

theorem not_dvd_inside {q u j : ℕ} (hj : 0 < j) (hjq : j < q) : ¬q ∣ q * u + j := by
  intro hdiv
  have hqu : q ∣ q * u := dvd_mul_right q u
  have hjdiv : q ∣ j := by simpa only [Nat.add_sub_cancel_left] using Nat.dvd_sub hdiv hqu
  have hle := Nat.le_of_dvd hj hjdiv
  omega

theorem positive_exact_run {M : ℕ} (q : PrimeUpTo M) (u : ℕ)
    (hu : ¬q.val.val ∣ u) (hu1 : ¬q.val.val ∣ u + 1) :
    StartEvent (valueBit (sample q)) (q.val.val * u + 1) (q.val.val - 1) ∧
      valueBit (sample q) (q.val.val * u + 1) = 0 ∧
      valueBit (sample q) (q.val.val * u + 1 + (q.val.val - 1)) = 1 := by
  let p : ℕ := q.val.val
  have hp : Nat.Prime p := q.property
  have hp2 : 2 ≤ p := hp.two_le
  have hprev : valueBit (sample q) (p * u + 1 - 1) = 1 := by
    rw [Nat.add_sub_cancel, valueBit_sample]
    exact parity_simple_multiple hp hu
  have hinside (j : ℕ) (hj : j < p - 1) : valueBit (sample q) (p * u + 1 + j) = 0 := by
    rw [valueBit_sample]
    have heq : p * u + 1 + j = p * u + (j + 1) := by omega
    rw [heq]
    exact parity_zero_of_not_dvd (not_dvd_inside (by omega) (by omega))
  have hfirst := hinside 0 (by omega)
  simp only [Nat.add_zero] at hfirst
  have hnext : valueBit (sample q) (p * u + 1 + (p - 1)) = 1 := by
    rw [valueBit_sample]
    have heq : p * u + 1 + (p - 1) = p * (u + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    rw [heq]
    exact parity_simple_multiple hp hu1
  refine ⟨⟨?_, ?_⟩, hfirst, hnext⟩
  · rw [hprev, hfirst, add_zero]
  · intro j hj
    rw [hinside j hj, hfirst]

end PaperP1.OneNegativePrime
