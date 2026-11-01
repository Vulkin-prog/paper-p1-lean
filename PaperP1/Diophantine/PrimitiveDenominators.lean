module

public import PaperP1.Arithmetic.DivisorSubpolynomial
public import PaperP1.Asymptotics.UniformReal
public import Mathlib.Data.Int.GCD

/-! # Primitive-coordinate denominator divisibility after bivariate elimination -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveDenominators

open Finset

theorem dvd_product_nat {q A C a b : ℕ} (m n : ℕ) (hab : a.Coprime b)
    (hleft : q ∣ A * a ^ m) (hright : q ∣ C * b ^ n) : q ∣ A * C := by
  have hpow := hab.pow m n
  have hl : q ∣ (A * C) * a ^ m := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using dvd_mul_of_dvd_left hleft C
  have hr : q ∣ (A * C) * b ^ n := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using dvd_mul_of_dvd_left hright A
  have h := Nat.dvd_gcd hl hr
  rw [Nat.gcd_mul_left, hpow.gcd_eq_one, mul_one] at h
  exact h

theorem dvd_product_int {q A C a b : ℤ} (m n : ℕ) (hab : a.natAbs.Coprime b.natAbs)
    (hleft : q ∣ A * a ^ m) (hright : q ∣ C * b ^ n) : q ∣ A * C := by
  apply Int.natAbs_dvd_natAbs.mp
  have hl := Int.natAbs_dvd_natAbs.mpr hleft
  have hr := Int.natAbs_dvd_natAbs.mpr hright
  simp only [Int.natAbs_mul, Int.natAbs_pow] at hl hr ⊢
  exact dvd_product_nat m n hab hl hr

def signedDivisors (D : ℤ) : Finset ℤ :=
  D.natAbs.divisors.biUnion fun d ↦ { (d : ℤ), -(d : ℤ) }

theorem mem_signedDivisors {D q : ℤ} (hD : D ≠ 0) (hdiv : q ∣ D) :
    q ∈ signedDivisors D := by
  have hqmem : q.natAbs ∈ D.natAbs.divisors :=
    Nat.mem_divisors.mpr ⟨Int.natAbs_dvd_natAbs.mpr hdiv, Int.natAbs_ne_zero.mpr hD⟩
  refine mem_biUnion.mpr ⟨q.natAbs, hqmem, ?_⟩
  rcases le_total 0 q with h | h
  · have heq : (q.natAbs : ℤ) = q := by rw [← Int.abs_eq_natAbs, abs_of_nonneg h]
    simp only [heq, mem_insert, mem_singleton, true_or]
  · have heq : -(q.natAbs : ℤ) = q := by rw [← Int.abs_eq_natAbs, abs_of_nonpos h, neg_neg]
    exact mem_insert_of_mem (mem_singleton.mpr heq.symm)

theorem signedDivisors_card (D : ℤ) : (signedDivisors D).card ≤ 2 * D.natAbs.divisors.card := by
  calc
    _ ≤ ∑ d ∈ D.natAbs.divisors, ({ (d : ℤ), -(d : ℤ) } : Finset ℤ).card := card_biUnion_le
    _ ≤ ∑ _d ∈ D.natAbs.divisors, 2 := sum_le_sum (fun d _ ↦ by
      simpa only [card_singleton] using (card_insert_le (d : ℤ) {-(d : ℤ)}))
    _ = _ := by simp only [sum_const, nsmul_eq_mul, Nat.cast_id]; ring

theorem finite_denominator_count {S : Finset ℤ} {A C a b : ℤ} (m n : ℕ)
    (hA : A ≠ 0) (hC : C ≠ 0) (hab : a.natAbs.Coprime b.natAbs)
    (hS : ∀ q ∈ S, q ≠ 0 ∧ q ∣ A * a ^ m ∧ q ∣ C * b ^ n) :
    S.card ≤ 2 * (A * C).natAbs.divisors.card := by
  have hsub : S ⊆ signedDivisors (A * C) := by
    intro q hq
    obtain ⟨hq0, hleft, hright⟩ := hS q hq
    exact mem_signedDivisors (mul_ne_zero hA hC) (dvd_product_int m n hab hleft hright)
  exact (card_le_card hsub).trans (signedDivisors_card _)

theorem polynomial_height_count (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A C a b : ℤ, ∀ m n : ℕ, ∀ S : Finset ℤ,
      A ≠ 0 → C ≠ 0 → a.natAbs.Coprime b.natAbs → (A * C).natAbs ≤ N ^ K →
      (∀ q ∈ S, q ≠ 0 ∧ q ∣ A * a ^ m ∧ q ∣ C * b ^ n) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨Nd, hNd⟩ := PaperP1.DivisorSubpolynomial.card_divisors_le_rpow_eventually K (ε / 2) (by positivity)
  obtain ⟨Nc, hNc⟩ := PaperP1.UniformReal.uniformSubpolynomialOn_le_rpow
    (PaperP1.ExpSqrtLog.uniformSubpolynomialOn_const (fun _ _ : ℕ ↦ True) 2) (ε / 2) (by positivity)
  refine ⟨max 1 (max Nd Nc), ?_⟩
  intro N hN A C a b m n S hA hC hab hheight hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : (2 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := (le_abs_self _).trans (hNc N (by omega) 0 trivial)
  have hd := hNd N (by omega) (A * C).natAbs hheight
  calc
    _ ≤ 2 * ((A * C).natAbs.divisors.card : ℝ) := by exact_mod_cast finite_denominator_count m n hA hC hab hS
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) := mul_le_mul hc hd (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.PrimitiveDenominators
