module

public import PaperP1.Asymptotics.PositiveUniversalPrivateObstruction
public import PaperP1.Asymptotics.PrintedAnchorObstructionParameters
public import PaperP1.Asymptotics.CriticalChannelPowers

/-! # Internal positive-constant universal randomized obstruction at the printed parameters

Every actual measurable private forcing and independent auxiliary law is
covered. The stronger printed1-o(1) coefficient remains unresolved.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositivePrintedRandomizedObstruction

open MeasureTheory PaperP1.Arithmetic PaperP1.Model PaperP1.RandomizedHybridField
  PaperP1.PrintedAnchorObstructionParameters
  PaperP1.LogFifthPivotCutoff

theorem printed_lower (C D a : ℝ) (hD : 0 ≤ D)
    (ha : 0 < a) (ha1 : a < 1 / 10) :
    ∃ r : ℝ, 0 < r ∧ ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L E M : ℕ, ∀ i : Fin 2,
      ((L + E + 2 : ℕ) : ℝ) ≤ D * Real.log N → 2 * N + (L + E + 2) ≤ M →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ anchor : PaperP1.AnchoredDyadicField.retainedBoundaries N (L + E + 2) (2 * (L + E + 2)) → Fin (L + i.val + 1),
      ∀ A : Data M (2 * (L + E + 2)) (L + i.val) (PaperP1.AnchoredDyadicField.retainedBoundaries N (L + E + 2) (2 * (L + E + 2)))
        (PaperP1.RandomizedDyadicHybridField.fullGood N (L + E + 2) (cutoff N)) anchor,
      ∀ (Ξ : Type*) [MeasurableSpace Ξ], ∀ μ : Measure Ξ, ∀ [IsProbabilityMeasure μ],
      ∀ b : Fin (L + i.val + 1) → F₂,
      ∀ g : PaperP1.AnchoredDyadicField.retainedBoundaries N (L + E + 2) (2 * (L + E + 2)) →
        (Fin (L + i.val + 1) → F₂) → Ξ → F₂,
      ∀ F : PaperP1.AnchoredDyadicField.retainedBoundaries N (L + E + 2) (2 * (L + E + 2)) →
        SampleSpace M → Ξ → SampleSpace M,
      (∀ j u s, MeasurableSet {ξ : Ξ | g j u ξ = s}) →
      (∀ j ω r s, MeasurableSet {ξ : Ξ | F j ω ξ r = s}) →
      (∀ j, j.val ∈ PaperP1.RandomizedDyadicHybridField.fullGood N (L + E + 2) (cutoff N) → ∀ ω ξ,
        PaperP1.PrivateValueSystem.valueSystem M (fun k : Fin (L + i.val + 1) ↦ j.val + k.val) (F j ω ξ) =
          PaperP1.RandomizedPrivatePalmForcing.orientedWord b
            (g j (PaperP1.PrivateValueSystem.valueSystem M (fun k : Fin (L + i.val + 1) ↦ j.val + k.val) ω) ξ)) →
      (∀ j, ∀ hj : j.val ∈ PaperP1.RandomizedDyadicHybridField.fullGood N (L + E + 2) (cutoff N),
        ∀ ω ξ, ∀ r : PrimeUpTo M, (∀ k, r ≠ fullPivots A j hj k) → F j ω ξ r = ω r) →
      r / 2 * nominal N L i.val a ≤
        PaperP1.PrivateForcingMeasureObservation.offsite μ b F := by
  obtain ⟨r, hr, NO, hO⟩ := PaperP1.PositiveUniversalPrivateObstruction.randomized_lower C D a hD ha ha1
  obtain ⟨NP, hP⟩ := uniform_parameters C D
  refine ⟨r, hr, max NO NP, ?_⟩
  intro N hN L E M i hwidth hM hband anchor A Ξ _ μ _ b g F hg hF hhit hout
  obtain ⟨hL, hcut⟩ := hP N (by omega) L E hband hwidth
  have hoff := hO N (by omega) L E (2 * (L + E + 2)) M i hL (by omega) hcut
    hwidth hM hband anchor A Ξ μ b g F hg hF hhit hout
  calc
    _ = r * (PaperP1.AnchoredPrivateField.rate (L + i.val)) ^ 2 / 2 * (N : ℝ) ^ (2 - a) := by
      rw [nominal_eq (by omega : 0 < N)]
      ring
    _ ≤ _ := hoff

theorem uniform_power_obstruction (C D α K : ℝ) (hD : 0 ≤ D) (hα : 0 < α) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L E M : ℕ, ∀ i : Fin 2,
      ((L + E + 2 : ℕ) : ℝ) ≤ D * Real.log N → 2 * N + (L + E + 2) ≤ M →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ anchor : PaperP1.AnchoredDyadicField.retainedBoundaries N (L + E + 2) (2 * (L + E + 2)) → Fin (L + i.val + 1),
      ∀ A : Data M (2 * (L + E + 2)) (L + i.val) (PaperP1.AnchoredDyadicField.retainedBoundaries N (L + E + 2) (2 * (L + E + 2)))
        (PaperP1.RandomizedDyadicHybridField.fullGood N (L + E + 2) (cutoff N)) anchor,
      ∀ (Ξ : Type*) [MeasurableSpace Ξ], ∀ μ : Measure Ξ, ∀ [IsProbabilityMeasure μ],
      ∀ b : Fin (L + i.val + 1) → F₂,
      ∀ g : PaperP1.AnchoredDyadicField.retainedBoundaries N (L + E + 2) (2 * (L + E + 2)) →
        (Fin (L + i.val + 1) → F₂) → Ξ → F₂,
      ∀ F : PaperP1.AnchoredDyadicField.retainedBoundaries N (L + E + 2) (2 * (L + E + 2)) →
        SampleSpace M → Ξ → SampleSpace M,
      (∀ j u s, MeasurableSet {ξ : Ξ | g j u ξ = s}) →
      (∀ j ω r s, MeasurableSet {ξ : Ξ | F j ω ξ r = s}) →
      (∀ j, j.val ∈ PaperP1.RandomizedDyadicHybridField.fullGood N (L + E + 2) (cutoff N) → ∀ ω ξ,
        PaperP1.PrivateValueSystem.valueSystem M (fun k : Fin (L + i.val + 1) ↦ j.val + k.val) (F j ω ξ) =
          PaperP1.RandomizedPrivatePalmForcing.orientedWord b
            (g j (PaperP1.PrivateValueSystem.valueSystem M (fun k : Fin (L + i.val + 1) ↦ j.val + k.val) ω) ξ)) →
      (∀ j, ∀ hj : j.val ∈ PaperP1.RandomizedDyadicHybridField.fullGood N (L + E + 2) (cutoff N),
        ∀ ω ξ, ∀ r : PrimeUpTo M, (∀ k, r ≠ fullPivots A j hj k) → F j ω ξ r = ω r) →
      K * (N : ℝ) ^ (-α) ≤
        PaperP1.PrivateForcingMeasureObservation.offsite μ b F := by
  let a := min (α / 2) (1 / 20)
  have ha : 0 < a := lt_min (by positivity) (by norm_num)
  have ha1 : a < 1 / 10 := (min_le_right _ _).trans_lt (by norm_num)
  have haα : a < α := (min_le_left _ _).trans_lt (by linarith only [hα])
  obtain ⟨r, hr, NC, hc⟩ := printed_lower C D a hD ha ha1
  let c := (r / 2) * (((2 : ℝ) ^ C)⁻¹) ^ 2 / 4
  have hcpos : 0 < c := by dsimp only [c]; positivity
  obtain ⟨NP, hp⟩ := HalfCountSchedule.factor_absorption (K / c) (-α) (α - a)
    (by linarith only [haα])
  refine ⟨max NC NP, ?_⟩
  intro N hN L E M i hwidth hM hcrit anchor A Ξ _ μ _ b g F hg hF hhit hout
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlower := hc N (by omega) L E M i hwidth hM hcrit anchor A Ξ μ b g F hg hF hhit hout
  have hnom := (div_le_iff₀ hn).mp (CriticalChannelPowers.nominal_lower (by omega : 2 ≤ N) hcrit)
  have hNomSquare : (((2 : ℝ) ^ C)⁻¹) ^ 2 ≤ ((N : ℝ) * (2 ^ L : ℝ)⁻¹) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith only [hnom]
  have hfac : (1 / 4 : ℝ) ≤ (2 ^ (2 * i.val) : ℝ)⁻¹ := by fin_cases i <;> norm_num
  have hm := mul_le_mul hfac hNomSquare (by positivity : (0 : ℝ) ≤ (((2 : ℝ) ^ C)⁻¹) ^ 2)
    (by positivity : (0 : ℝ) ≤ (2 ^ (2 * i.val) : ℝ)⁻¹)
  have hminor : c * (N : ℝ) ^ (-a) ≤ (r / 2) * nominal N L i.val a := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ r / 2))
      (Real.rpow_nonneg hn.le (-a))
    simpa only [c, nominal, mul_assoc, mul_left_comm, div_eq_mul_inv, one_mul] using hh
  have hpower := hp N (by omega)
  rw [show -α + (α - a) = -a by ring] at hpower
  have hmul := mul_le_mul_of_nonneg_left hpower hcpos.le
  have hid : c * (K / c * (N : ℝ) ^ (-α)) = K * (N : ℝ) ^ (-α) := by field_simp
  rw [hid] at hmul
  exact hmul.trans (hminor.trans hlower)

end PaperP1.PositivePrintedRandomizedObstruction
