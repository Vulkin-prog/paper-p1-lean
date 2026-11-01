module

public import PaperP1.Model.ConditionalRunBudget
public import PaperP1.Asymptotics.ConditionalPoolLower

/-! # Companion T21.2: actual conditional ranks, means and the matching critical scale -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConditionalRankTheorem

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.ConditionalWindowRank
  PaperP1.OldValuePrimeBudget PaperP1.WindowPoolCount PaperP1.ConditionalRunProbability
  PaperP1.ConditionalCountMean PaperP1.ConditionalRunBudget PaperP1.CriticalBandScale
  PaperP1.ConditionalPoolTerm PaperP1.ExponentialSupportSlope

def FiniteConclusion (N L : ℕ) (A : Finset ℕ) : Prop :=
  let R := rawValues A L
  let O := contactStarts N L A
  (∀ x ∈ dyadicBlock N, conditionalNullity R (x - 1) (L + 1) ≤
      (supportedIndices R (x - 1) (L + 1)).card - 1) ∧
    ∀ a : SampleSpace (dyadicCutoff N L),
      (∀ x ∈ dyadicBlock N,
        (conditionalStartProbability R a x L = 0 ∨ conditionalStartProbability R a x L =
          (2 ^ conditionalNullity R (x - 1) (L + 1) : ℝ) / (2 ^ L : ℝ)) ∧
        ((supportedIndices R (x - 1) (L + 1)).card ≤ 1 →
          conditionalStartProbability R a x L = (2 ^ L : ℝ)⁻¹)) ∧
      ∀ T : ℕ, 1 ≤ T →
        conditionalCountExpectation R a (dyadicBlock N) L ≤
          (N : ℝ) * (2 ^ L : ℝ)⁻¹ + O.card + (largeStarts N L R O T).card + term N L T A ∧
        conditionalCountExpectation R a (dyadicBlock N) L ≤
          (N : ℝ) * (2 ^ L : ℝ)⁻¹ + O.card + (largeStarts N L R O T).card +
            (2 ^ L : ℝ)⁻¹ * slope T * (L + 1) * (poolValues R (L + 1) (3 * N)).card

theorem rawValues_le_cutoff {N L : ℕ} {A : Finset ℕ} (hA : A ⊆ dyadicBlock N) :
    ∀ n ∈ rawValues A L, n ≤ dyadicCutoff N L := by
  intro n hn
  obtain ⟨x, hx, hn⟩ := mem_biUnion.mp hn
  have hxb := mem_Ico.mp (hA hx)
  have hnb := mem_Ico.mp hn
  unfold dyadicCutoff
  omega

theorem finite_conclusion {N L : ℕ} {A : Finset ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hLN : L ≤ N) (hA : A ⊆ dyadicBlock N) : FiniteConclusion N L A := by
  refine ⟨fun x _ ↦ conditionalNullity_le _ _ _, fun a ↦ ⟨?_, ?_⟩⟩
  · intro x hx
    have hxb := mem_Ico.mp hx
    have hcut : x + L ≤ dyadicCutoff N L := by unfold dyadicCutoff; omega
    exact ⟨conditionalStartProbability_zero_or_pow (by omega) hL hcut (rawValues_le_cutoff hA) a,
      fun hcard ↦ conditionalStartProbability_nominal (by omega) hL hcut (rawValues_le_cutoff hA) a hcard⟩
  · intro T hT
    exact ⟨conditional_count_bound hN hL hLN le_rfl (rawValues_le_cutoff hA) a hT (contactStarts_subset N L A),
      conditional_count_bound_sharp hN hL hLN le_rfl (rawValues_le_cutoff hA) a (contactStarts_subset N L A)⟩

theorem finite_conditions (C : ℝ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      3 ≤ N ∧ 0 < L ∧ L ≤ N := by
  obtain ⟨Nscale, hscale⟩ := critical_band_scale C
  obtain ⟨Npoly, hpoly⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le 1 1 1 (by norm_num)
  obtain ⟨Nlog, hlog⟩ := ElementaryLogGrowth.log_ge_eventually (2 / lowerScale)
  refine ⟨max 3 (max Nscale (max Npoly Nlog)), le_max_left _ _, ?_⟩
  intro N hN L hband
  obtain ⟨hlo, hhi⟩ := hscale N (by omega) L hband
  have hpolyN := hpoly N (by omega) L hhi
  have hwidth : (L + 1 : ℝ) ≤ N := by
    simpa only [one_mul, pow_one, Real.rpow_one, abs_of_nonneg (by positivity : (0 : ℝ) ≤ L + 1)] using hpolyN
  have htwo : (2 : ℝ) ≤ lowerScale * Real.log N := by
    have h := (div_le_iff₀ lowerScale_pos).mp (hlog N (by omega)).1
    nlinarith
  have hLpos : 0 < L := by
    have hB : 2 ≤ L + 1 := by exact_mod_cast htwo.trans hlo
    omega
  have hLN : L + 1 ≤ N := by exact_mod_cast hwidth
  exact ⟨by omega, hLpos, by omega⟩

theorem floor_conditions (C δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      1 ≤ ⌊(1 - δ) * (L : ℝ)⌋₊ ∧ ⌊(1 - δ) * (L : ℝ)⌋₊ ≤ L := by
  obtain ⟨Nscale, hscale⟩ := critical_band_scale C
  obtain ⟨Nlog, hlog⟩ := ElementaryLogGrowth.log_ge_eventually ((2 / (1 - δ) + 1) / lowerScale)
  refine ⟨max Nscale Nlog, ?_⟩
  intro N hN L hband
  have hlo := (hscale N (by omega) L hband).1
  have hlarge := (div_le_iff₀ lowerScale_pos).mp (hlog N (by omega)).1
  have hL : 2 / (1 - δ) ≤ (L : ℝ) := by
    have hcast : ((L + 1 : ℕ) : ℝ) = (L : ℝ) + 1 := by norm_cast
    rw [hcast] at hlo
    linarith
  have harg : 0 ≤ (1 - δ) * (L : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg L)
  constructor
  · apply (Nat.le_floor_iff harg).mpr
    have h := (div_le_iff₀ (sub_pos.mpr hδ1)).mp hL
    norm_num
    nlinarith
  · have hfloor := floor_threshold_le L δ hδ1.le
    have hupper : ((⌊(1 - δ) * (L : ℝ)⌋₊ : ℕ) : ℝ) ≤ L := by
      have hL0 := Nat.cast_nonneg (α := ℝ) L
      nlinarith
    exact_mod_cast hupper

/-- Every source conclusion, with the old windows and all realizable old vectors uniform. -/
theorem companion_T21_2 (C : ℝ) (j : ℕ) (δ ε : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ A : Finset ℕ, A ⊆ dyadicBlock N → A.card ≤ j →
        FiniteConclusion N L A ∧
          (1 ≤ ⌊(1 - δ) * (L : ℝ)⌋₊ ∧ ⌊(1 - δ) * (L : ℝ)⌋₊ ≤ L) ∧
          (N : ℝ) ^ (1 / 2 - δ - ε) ≤ term N L ⌊(1 - δ) * (L : ℝ)⌋₊ A ∧
          term N L ⌊(1 - δ) * (L : ℝ)⌋₊ A ≤ (N : ℝ) ^ (1 / 2 - δ + ε) := by
  obtain ⟨Nfinite, hNfinite, hfinite⟩ := finite_conditions C
  obtain ⟨Nfloor, hfloor⟩ := floor_conditions C δ hδ hδ1
  obtain ⟨Nupper, _, hupper⟩ := fractional_term_le_power_critical C j δ ε hδ hδ1 hε
  obtain ⟨Nlower, _, hlower⟩ := ConditionalPoolLower.term_lower_eventually C δ ε hδ.le hε
  refine ⟨max Nfinite (max Nfloor (max Nupper Nlower)), by omega, ?_⟩
  intro N hN L hband A hA hj
  obtain ⟨hN3, hLpos, hLN⟩ := hfinite N (by omega) L hband
  exact ⟨finite_conclusion (by omega) hLpos hLN hA, hfloor N (by omega) L hband,
    hlower N (by omega) L hband A, hupper N (by omega) L hband A hA hj⟩

end PaperP1.ConditionalRankTheorem
