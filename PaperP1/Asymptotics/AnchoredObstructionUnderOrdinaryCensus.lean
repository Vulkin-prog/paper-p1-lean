module

public import PaperP1.Asymptotics.AnchoredObstructionFromCensus

/-! # The deterministic part of T19.17 under the independent ordinary source census

The census hypothesis is solely about positive integer arguments and
ordinary largest prime factors, with no anchor, forcing, probability or
cost in it. Every other step of the two actual unsigned obstructions is
proved. No ordinary short-interval abundance theorem is asserted here.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnchoredObstructionUnderOrdinaryCensus

open PaperP1.Arithmetic PaperP1.Model PaperP1.AnchoredPrivateField
  PaperP1.OrdinarySmoothSourcePopulation PaperP1.LogFifthPivotCutoff

def OrdinaryCensusDensity (C a : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ i : Fin 2,
    |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((missingCandidates N (L + i.val) ((N : ℝ) ^ a)).card : ℝ) ≤ τ * N

theorem rate_factor (L i : ℕ) : rate (L + i) = rate L * (2 ^ i : ℝ)⁻¹ := by
  simp only [rate, pow_add, mul_inv_rev, mul_comm]

theorem nominal_scale_identity {N : ℕ} (hN : 0 < N) (L i : ℕ) (a : ℝ) :
    (rate (L + i)) ^ 2 * (N : ℝ) ^ (2 - a) =
      (2 ^ (2 * i) : ℝ)⁻¹ * ((N : ℝ) * (2 ^ L : ℝ)⁻¹) ^ 2 * (N : ℝ) ^ (-a) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hi : (2 ^ (2 * i) : ℝ)⁻¹ = ((2 ^ i : ℝ)⁻¹) ^ 2 := by
    rw [Nat.mul_comm 2 i, pow_mul, inv_pow]
  rw [rate_factor, hi]
  simp only [rate, mul_pow, Real.rpow_sub hn, Real.rpow_two,
    Real.rpow_neg (Nat.cast_nonneg N), div_eq_mul_inv]
  ring

theorem deterministic_under_census (C D a : ℝ) (hD : 0 ≤ D)
    (ha : 0 < a) (ha1 : a < 1 / 10) (hCensus : OrdinaryCensusDensity C a)
    (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L E Y M : ℕ, ∀ i : Fin 2,
      1 ≤ L → L + E + 2 ≤ Y → Y ≤ cutoff N →
      ((L + E + 2 : ℕ) : ℝ) ≤ D * Real.log N → 2 * N + (L + E + 2) ≤ M →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ anchor : PaperP1.AnchoredDyadicField.retainedBoundaries N (L + E + 2) Y → Fin (L + i.val + 1),
      ∀ A : Data M Y (L + i.val) (PaperP1.AnchoredDyadicField.retainedBoundaries N (L + E + 2) Y) anchor,
      ∀ b : Fin (L + i.val + 1) → F₂,
      (1 - η) * (rate (L + i.val)) ^ 2 * (N : ℝ) ^ (2 - a) ≤ offsite A b := by
  let t : ℝ := min 1 (η / 3)
  have ht : 0 < t := lt_min zero_lt_one (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  obtain ⟨NO, hO⟩ := PaperP1.AnchoredObstructionFromCensus.uniform_census_implication D a t hD ha ha1 ht ht1
  obtain ⟨NM, hM⟩ := hCensus (t / 2) (by positivity)
  refine ⟨max NO NM, ?_⟩
  intro N hN L E Y M i hL hBY hYZ hwidth hcut hband anchor A b
  have hival := i.isLt
  have hmissing := hM N (by omega) L i hband
  have hoff := hO N (by omega) (L + E + 2) Y (L + i.val) M (by omega) (by omega)
    hBY hYZ hwidth hcut hmissing anchor A b
  have hco : 1 - η ≤ 1 - 3 * t := by
    have hh : t ≤ η / 3 := min_le_right _ _
    linarith only [hh]
  have hm := mul_le_mul_of_nonneg_right hco
    (by positivity : (0 : ℝ) ≤ (rate (L + i.val)) ^ 2 * (N : ℝ) ^ (2 - a))
  have hm' : (1 - η) * (rate (L + i.val)) ^ 2 * (N : ℝ) ^ (2 - a) ≤
      (1 - 3 * t) * (rate (L + i.val)) ^ 2 * (N : ℝ) ^ (2 - a) := by
    simpa only [mul_assoc] using hm
  exact hm'.trans hoff

end PaperP1.AnchoredObstructionUnderOrdinaryCensus
