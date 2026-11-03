module

public import PaperP1.Arithmetic.OffsetLineDivisorCount
public import PaperP1.Asymptotics.CriticalPolynomialScale

/-! # Uniform bounded multiplicity on every actual collinear offset subfamily -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetLineDivisorCountUniform

universe u

theorem uniform_lines (C τ : ℝ) (hτ : 0 < τ) (A K : ℕ) (hA : 1 ≤ A) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ (ι : Type u) (S : Finset ι) (s t : ι → ℤ) (g : ι → ℕ),
      ∀ x y : ℤ, (N : ℤ) ≤ (A : ℤ) * x → x.natAbs ≤ A * N → y.natAbs ≤ A * N →
      (∀ i ∈ S, (s i).natAbs ≤ K * (L + 1)) → (∀ i ∈ S, (t i).natAbs ≤ K * (L + 1)) →
      (S : Set ι).Pairwise (fun i j ↦ (g i).Coprime (g j)) →
      (∀ i ∈ S, (g i : ℤ) ∣ x + s i) → (∀ i ∈ S, (g i : ℤ) ∣ y + t i) →
      (∀ i ∈ S, (N : ℝ) ^ τ ≤ (g i : ℝ)) →
      (∀ i ∈ S, ∀ j ∈ S, (s i, t i) ≠ (s j, t j) →
        (x + s i) * (y + t j) ≠ (x + s j) * (y + t i)) →
      (∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S,
        (s j - s i) * (t k - t i) = (t j - t i) * (s k - s i)) →
      (S.card : ℝ) ≤ 3 / τ := by
  obtain ⟨NP, hp⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((A * K : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  refine ⟨max (4 * A + 2) (max 2 NP), by omega, ?_⟩
  intro N hN L hband ι S s t g x y hxlo hx hy hs ht hcop hdivs hdivt hlarge hno hcol
  have hAB : A * (K * (L + 1)) < N := by
    have hh := hp N (by omega) L hband
    rw [pow_one, ← Nat.cast_mul, Nat.cast_lt] at hh
    simpa only [mul_assoc] using hh
  have hB : K * (L + 1) < N := by nlinarith only [hAB, hA]
  have hvalues (i : ι) (hi : i ∈ S) : x + s i ≠ 0 := by
    intro hz
    have hh : |s i| ≤ ((K * (L + 1) : ℕ) : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hs i hi
    have hlo := (abs_le.mp hh).1
    have hxle : x ≤ ((K * (L + 1) : ℕ) : ℤ) := by omega
    have hm := mul_le_mul_of_nonneg_left hxle (Int.natCast_nonneg A)
    have hABZ : (A : ℤ) * ((K * (L + 1) : ℕ) : ℤ) < N := by exact_mod_cast hAB
    omega
  exact OffsetLineDivisorCount.collinear_card_bound S s t g N A (K * (L + 1)) τ
    (by omega) hA hB (by omega) hτ x y hvalues hx hy hs ht hcop hdivs hdivt hlarge hno hcol

end PaperP1.OffsetLineDivisorCountUniform
