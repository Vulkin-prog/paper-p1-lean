module

public import PaperP1.Arithmetic.SourceSupportedCoefficientPool
public import PaperP1.Arithmetic.FixedSourceCertificate
public import PaperP1.Arithmetic.DivisorSubpolynomial
public import PaperP1.Arithmetic.SmoothSupportBounds
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # A common subpower coefficient pool before every actual fixed source tuple -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceSupportedCoefficientCount

open Finset PaperP1.SourceSupportedCoefficientPool PaperP1.CriticalBandScale

theorem position_count (s R : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((positions (ι := Fin s × Fin (L + 1)) R).card : ℝ) ≤ (N : ℝ) ^ ε := by
  let A : ℕ := (R + 1) * (s + 1) ^ R
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le A R ε hε
  obtain ⟨NG, hg⟩ := critical_band_scale C
  refine ⟨max NP NG, ?_⟩
  intro N hN L hband
  have hbase : s * (L + 1) + 1 ≤ (s + 1) * (L + 1) := by nlinarith
  have hcard : (positions (ι := Fin s × Fin (L + 1)) R).card ≤ A * (L + 1) ^ R := by
    calc
      _ ≤ (R + 1) * (s * (L + 1) + 1) ^ R := by
        simpa only [positions, card_univ, Fintype.card_prod, Fintype.card_fin] using
          BoundedSubsets.card_sets (univ : Finset (Fin s × Fin (L + 1))) R
      _ ≤ (R + 1) * ((s + 1) * (L + 1)) ^ R :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase R)
      _ = _ := by simp only [A, mul_pow, mul_assoc]
  have hpoly := hp N (by omega) L (hg N (by omega) L hband).2
  calc
    _ ≤ ((A * (L + 1) ^ R : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (A : ℝ) * (L + 1 : ℝ) ^ R := by push_cast; rfl
    _ ≤ _ := (le_abs_self _).trans hpoly

theorem uniform_count (s R : ℕ) (D C ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → (H : ℝ) ≤ D * (L + 1 : ℕ) →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ Ico N (2 * N)) →
        ((pool (FixedSourceCertificate.sourceValues x (L + 1)) H R).card : ℝ) ≤ (N : ℝ) ^ ε := by
  let Kp := ⌈D * upperScale * Real.log 4⌉₊
  obtain ⟨NP, hp⟩ := position_count s R C (ε / 3) (by positivity)
  obtain ⟨ND, hd⟩ := DivisorSubpolynomial.card_divisors_le_rpow_eventually (2 * R) (ε / 3) (by positivity)
  obtain ⟨NS, hs⟩ := DivisorSubpolynomial.card_divisors_le_rpow_eventually Kp (ε / 3) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 0
  refine ⟨max 3 (max NP (max ND (max NS NG))), by omega, ?_⟩
  intro N hN L H hband hH x hx
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hgeom := hg N (by omega) L hband
  have hLN : L ≤ N := by have h := hgeom.2.2.2.1; omega
  have hB := hgeom.2.2.2.2.2
  have hHlog : (H : ℝ) ≤ (D * upperScale) * Real.log N :=
    hH.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hB hD)
  have hprimorial : primorial H ≤ N ^ Kp := (primorial_le_four_pow H).trans
    (SmoothSupportBounds.four_pow_cutoff_le_polynomial (by omega) hHlog (Nat.le_ceil _))
  have hprime := hs N (by omega) (primorial H) hprimorial
  let v := FixedSourceCertificate.sourceValues x (L + 1)
  have hprod : ∀ A ∈ positions (ι := Fin s × Fin (L + 1)) R, A.prod v ≤ N ^ (2 * R) := by
    intro A hA
    have hAR := (mem_positions R A).mp hA
    calc
      _ ≤ ∏ _i ∈ A, N ^ 2 := prod_le_prod fun i _ ↦ FixedSourceCertificate.sourceValues_le_square x (by omega) hLN hx i
      _ = N ^ (2 * A.card) := by rw [prod_const, ← pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right (by omega : 0 < N) (Nat.mul_le_mul_left 2 hAR)
  have hdiv : ∀ A ∈ positions (ι := Fin s × Fin (L + 1)) R, ((A.prod v).divisors.card : ℝ) ≤ (N : ℝ) ^ (ε / 3) :=
    fun A hA ↦ hd N (by omega) (A.prod v) (hprod A hA)
  have hfinite := card_pool_real v H R ((N : ℝ) ^ (ε / 3)) hdiv
  have hpositions := hp N (by omega) L hband
  calc
    _ ≤ ((positions (ι := Fin s × Fin (L + 1)) R).card : ℝ) *
        ((primorial H).divisors.card : ℝ) * (N : ℝ) ^ (ε / 3) := hfinite
    _ ≤ (N : ℝ) ^ (ε / 3) * (N : ℝ) ^ (ε / 3) * (N : ℝ) ^ (ε / 3) := by gcongr
    _ = _ := by rw [← Real.rpow_add hn, ← Real.rpow_add hn]; congr 1; ring

end PaperP1.SourceSupportedCoefficientCount
