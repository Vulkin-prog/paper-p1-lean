module

public import PaperP1.Coding.UniformLocalRigidity
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# General and critical logarithmic window regimes

The uniform window theorem implies the exact asymptotic thresholds in
article Lemma 2.1. The critical length is treated both by its normalized
limit and by the literal `log N / log 2 + o(log N)` hypothesis.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalRigidityRegimes

open PaperP1.Arithmetic Filter Real Asymptotics
open LocalRigidityThreshold UniformLocalRigidity WindowRelationCode

local instance rigidityRegimesPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem uniform_relation_rank_lt_paper (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (t : ℕ) (hct : c < 2 - (2 : ℝ) ^ (1 - (t : ℤ))) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ U B : ℕ,
      a * N ≤ (U : ℝ) → (B : ℝ) ≤ c * Real.log N →
        Module.finrank F₂ (windowRelationCode U B) < t := by
  apply uniform_relation_rank_lt a c ha hc t
  simpa only [griesmerFactor_eq_paper] using hct

/-- A normalized logarithmic length limit, with every admissible base quantified
after the common threshold. -/
theorem relation_rank_lt_of_length_ratio (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (t : ℕ) (hct : c < griesmerFactor t) (B : ℕ → ℕ)
    (hB : Tendsto (fun N : ℕ ↦ (B N : ℝ) / Real.log N) atTop (nhds c)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ U : ℕ,
      a * N ≤ (U : ℝ) → Module.finrank F₂ (windowRelationCode U (B N)) < t := by
  let c' := (c + griesmerFactor t) / 2
  have hc' : 0 < c' := by dsimp [c']; linarith
  have hcc' : c < c' := by dsimp [c']; linarith
  have hc't : c' < griesmerFactor t := by dsimp [c']; linarith
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hB.eventually (eventually_lt_nhds hcc'))
  obtain ⟨N₂, hN₂⟩ := uniform_relation_rank_lt a c' ha hc' t hc't
  refine ⟨max 2 (max N₁ N₂), fun N hN U hbase ↦ ?_⟩
  have hNtwo : 2 ≤ N := by omega
  have hNone : N₁ ≤ N := by omega
  have hNtwo' : N₂ ≤ N := by omega
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  exact hN₂ N hNtwo' U (B N) hbase ((div_lt_iff₀ hlog).mp (hN₁ N hNone)).le

theorem critical_coefficient_lt : 1 / Real.log 2 < griesmerFactor 2 := by
  rw [griesmerFactor_two]
  apply (div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  nlinarith [Real.log_two_gt_d9]

theorem critical_relation_rank_le_one (a : ℝ) (ha : 0 < a) (B : ℕ → ℕ)
    (hB : Tendsto (fun N : ℕ ↦ (B N : ℝ) / Real.log N)
      atTop (nhds (1 / Real.log 2))) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ U : ℕ,
      a * N ≤ (U : ℝ) → Module.finrank F₂ (windowRelationCode U (B N)) ≤ 1 := by
  have hc : (0 : ℝ) < 1 / Real.log 2 := div_pos zero_lt_one (Real.log_pos (by norm_num))
  obtain ⟨N₀, hN₀⟩ := relation_rank_lt_of_length_ratio a (1 / Real.log 2) ha hc 2
    critical_coefficient_lt B hB
  refine ⟨N₀, fun N hN U hbase ↦ ?_⟩
  have h := hN₀ N hN U hbase
  omega

theorem length_ratio_tendsto_of_critical_error (B : ℕ → ℕ)
    (hB : (fun N : ℕ ↦ (B N : ℝ) - Real.log N / Real.log 2)
      =o[atTop] (fun N : ℕ ↦ Real.log N)) :
    Tendsto (fun N : ℕ ↦ (B N : ℝ) / Real.log N)
      atTop (nhds (1 / Real.log 2)) := by
  have herror : Tendsto (fun N : ℕ ↦
      ((B N : ℝ) - Real.log N / Real.log 2) / Real.log N) atTop (nhds 0) := by
    simpa only [Pi.div_apply] using hB.tendsto_div_nhds_zero
  have hsum := herror.add_const (1 / Real.log 2)
  have heq : (fun N : ℕ ↦ (B N : ℝ) / Real.log N) =ᶠ[atTop]
      (fun N : ℕ ↦ ((B N : ℝ) - Real.log N / Real.log 2) / Real.log N +
        1 / Real.log 2) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    field_simp [hl.ne', h2.ne']
    ring
  exact Tendsto.congr' heq.symm (by simpa only [zero_add] using hsum)

/-- Literal critical-length hypothesis in article Lemma 2.1. -/
theorem critical_relation_rank_le_one_of_error (a : ℝ) (ha : 0 < a) (B : ℕ → ℕ)
    (hB : (fun N : ℕ ↦ (B N : ℝ) - Real.log N / Real.log 2)
      =o[atTop] (fun N : ℕ ↦ Real.log N)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ U : ℕ,
      a * N ≤ (U : ℝ) → Module.finrank F₂ (windowRelationCode U (B N)) ≤ 1 :=
  critical_relation_rank_le_one a ha B (length_ratio_tendsto_of_critical_error B hB)

theorem length_ratio_tendsto_of_asymptotic (c : ℝ) (hc : 0 < c) (B : ℕ → ℕ)
    (hB : (fun N : ℕ ↦ (B N : ℝ)) ~[atTop] (fun N : ℕ ↦ c * Real.log N)) :
    Tendsto (fun N : ℕ ↦ (B N : ℝ) / Real.log N) atTop (nhds c) := by
  have hnonzero : ∀ᶠ N : ℕ in atTop, c * Real.log N ≠ 0 := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact mul_ne_zero hc.ne' (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have hratio := (isEquivalent_iff_tendsto_one hnonzero).mp hB
  have hmul := hratio.mul_const c
  have heq : (fun N : ℕ ↦ (B N : ℝ) / Real.log N) =ᶠ[atTop]
      (fun N : ℕ ↦ ((B N : ℝ) / (c * Real.log N)) * c) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    field_simp [hc.ne', hl.ne']
  exact Tendsto.congr' heq.symm (by simpa only [Pi.div_apply, one_mul] using hmul)

/-- The literal general B ~ c log N assertion and the exact paper threshold. -/
theorem relation_rank_lt_of_length_asymptotic (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (t : ℕ) (hct : c < 2 - (2 : ℝ) ^ (1 - (t : ℤ))) (B : ℕ → ℕ)
    (hB : (fun N : ℕ ↦ (B N : ℝ)) ~[atTop] (fun N : ℕ ↦ c * Real.log N)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ U : ℕ,
      a * N ≤ (U : ℝ) → Module.finrank F₂ (windowRelationCode U (B N)) < t := by
  apply relation_rank_lt_of_length_ratio a c ha hc t
    (by simpa only [griesmerFactor_eq_paper] using hct) B
  exact length_ratio_tendsto_of_asymptotic c hc B hB

/-- One threshold works for every length in a fixed critical band. -/
theorem critical_band_relation_rank_le_one (a C : ℝ) (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ U L : ℕ,
      a * N ≤ (U : ℝ) → |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        Module.finrank F₂ (windowRelationCode U (L + 1)) ≤ 1 := by
  let c₀ := 1 / Real.log 2
  let c := (c₀ + griesmerFactor 2) / 2
  have hc₀ : 0 < c₀ := div_pos zero_lt_one (Real.log_pos (by norm_num))
  have hgap : 0 < c - c₀ := by
    dsimp [c, c₀]
    linarith [critical_coefficient_lt]
  have hc : 0 < c := by linarith
  have hct : c < griesmerFactor 2 := by
    dsimp [c, c₀]
    linarith [critical_coefficient_lt]
  obtain ⟨N₁, hN₁⟩ := uniform_relation_rank_lt a c ha hc 2 hct
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp
    (PrimeLogBudget.log_nat_tendsto_atTop.eventually
      (eventually_ge_atTop ((C + 1) / (c - c₀))))
  refine ⟨max N₁ N₂, fun N hN U L hbase hband ↦ ?_⟩
  have hn₁ : N₁ ≤ N := by omega
  have hn₂ : N₂ ≤ N := by omega
  have hconstant : C + 1 ≤ (c - c₀) * Real.log N := by
    have h := (div_le_iff₀ hgap).mp (hN₂ N hn₂)
    nlinarith
  have hlength := (abs_le.mp hband).2
  have hidentity : Real.log N / Real.log 2 = c₀ * Real.log N := by dsimp [c₀]; ring
  rw [hidentity] at hlength
  have hwidth : ((L + 1 : ℕ) : ℝ) ≤ c * Real.log N := by
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hr := hN₁ N hn₁ U (L + 1) hbase hwidth
  omega

end PaperP1.LocalRigidityRegimes
