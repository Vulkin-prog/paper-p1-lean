module

public import PaperP1.Arithmetic.SourceSupportedCoefficientPool
public import PaperP1.Arithmetic.FixedSourceCertificate
public import PaperP1.Arithmetic.DivisorSubpolynomial
public import PaperP1.Arithmetic.SmoothSupportBounds
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # Common source coefficient pools under an upper logarithmic width alone and explicit actual source heights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogarithmicSourceCoefficientCount

open Finset PaperP1.SourceSupportedCoefficientPool PaperP1.CriticalBandScale

theorem position_count (s R : ℕ) (D ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ D * Real.log N →
      ((positions (ι := Fin s × Fin (L + 1)) R).card : ℝ) ≤ (N : ℝ) ^ ε := by
  let A : ℕ := (R + 1) * (s + 1) ^ R
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    D hD A R ε hε
  refine ⟨NP, ?_⟩
  intro N hN L hwidth
  have hbase : s * (L + 1) + 1 ≤ (s + 1) * (L + 1) := by nlinarith
  have hcard : (positions (ι := Fin s × Fin (L + 1)) R).card ≤ A * (L + 1) ^ R := by
    calc
      _ ≤ (R + 1) * (s * (L + 1) + 1) ^ R := by
        simpa only [positions, card_univ, Fintype.card_prod, Fintype.card_fin] using
          BoundedSubsets.card_sets (univ : Finset (Fin s × Fin (L + 1))) R
      _ ≤ (R + 1) * ((s + 1) * (L + 1)) ^ R :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase R)
      _ = _ := by simp only [A, mul_pow, mul_assoc]
  have hpoly := hp N hN L hwidth
  calc
    _ ≤ ((A * (L + 1) ^ R : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (A : ℝ) * (L + 1 : ℝ) ^ R := by push_cast; rfl
    _ ≤ _ := (le_abs_self _).trans hpoly

theorem uniform_count (s R : ℕ) (D E ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ D * Real.log N → (H : ℝ) ≤ E * Real.log N →
      ∀ v : Fin s × Fin (L + 1) → ℕ, (∀ i, v i ≤ N ^ 2) →
        ((pool v H R).card : ℝ) ≤ (N : ℝ) ^ ε := by
  let Kp := ⌈E * Real.log 4⌉₊
  obtain ⟨NP, hp⟩ := position_count s R D (ε / 3) hD (by positivity)
  obtain ⟨ND, hd⟩ := DivisorSubpolynomial.card_divisors_le_rpow_eventually (2 * R) (ε / 3) (by positivity)
  obtain ⟨NS, hs⟩ := DivisorSubpolynomial.card_divisors_le_rpow_eventually Kp (ε / 3) (by positivity)
  refine ⟨max 3 (max NP (max ND NS)), by omega, ?_⟩
  intro N hN L H hwidth hH v hv
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hprimorial : primorial H ≤ N ^ Kp := (primorial_le_four_pow H).trans
    (SmoothSupportBounds.four_pow_cutoff_le_polynomial (by omega) hH (Nat.le_ceil _))
  have hprime := hs N (by omega) (primorial H) hprimorial
  have hprod : ∀ A ∈ positions (ι := Fin s × Fin (L + 1)) R, A.prod v ≤ N ^ (2 * R) := by
    intro A hA
    have hAR := (mem_positions R A).mp hA
    calc
      _ ≤ ∏ _i ∈ A, N ^ 2 := prod_le_prod fun i _ ↦ hv i
      _ = N ^ (2 * A.card) := by rw [prod_const, ← pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right (by omega : 0 < N) (Nat.mul_le_mul_left 2 hAR)
  have hdiv : ∀ A ∈ positions (ι := Fin s × Fin (L + 1)) R, ((A.prod v).divisors.card : ℝ) ≤ (N : ℝ) ^ (ε / 3) :=
    fun A hA ↦ hd N (by omega) (A.prod v) (hprod A hA)
  have hfinite := card_pool_real v H R ((N : ℝ) ^ (ε / 3)) hdiv
  have hpositions := hp N (by omega) L hwidth
  calc
    _ ≤ ((positions (ι := Fin s × Fin (L + 1)) R).card : ℝ) *
        ((primorial H).divisors.card : ℝ) * (N : ℝ) ^ (ε / 3) := hfinite
    _ ≤ (N : ℝ) ^ (ε / 3) * (N : ℝ) ^ (ε / 3) * (N : ℝ) ^ (ε / 3) := by gcongr
    _ = _ := by rw [← Real.rpow_add hn, ← Real.rpow_add hn]; congr 1; ring

end PaperP1.LogarithmicSourceCoefficientCount
