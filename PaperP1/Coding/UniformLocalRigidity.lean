module

public import PaperP1.Coding.LocalRigidityThreshold
public import PaperP1.Coding.WindowRelationMonotone
public import PaperP1.Asymptotics.LogarithmicWindowCap

/-!
# Uniform local relation rigidity

A single threshold controls every window of length at most c log N, at every
base U at least a N. The sharp condition is c < 2(1-2^(-t)). Only the lower
macroscopic bound on U is needed. The theorem uses the proved PNT, exact
Griesmer factor and extension of actual square relations by zero.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformLocalRigidity

open PaperP1.Arithmetic Filter Real LocalDefectBound
open LocalRigidityThreshold WindowRelationMonotone WindowRelationCode
open LogarithmicWindowCap PrimeLogBudget

local instance uniformRigidityPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem relation_rank_lt_eventually (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (t : ℕ) (hct : c < griesmerFactor t) :
    ∀ᶠ N : ℕ in atTop, ∀ U B : ℕ,
      a * N ≤ (U : ℝ) → (B : ℝ) ≤ c * Real.log N →
        Module.finrank F₂ (windowRelationCode U B) < t := by
  have hleft := cap_prime_budget_tendsto c hc t
  have hright : Tendsto (fun N : ℕ ↦ Real.log (a * N) * griesmerFactor t / Real.log N)
      atTop (nhds (griesmerFactor t)) := by
    have h := (log_mul_div_log_tendsto a ha).mul_const (griesmerFactor t)
    simpa only [one_mul, div_mul_eq_mul_div] using h
  have hpositive := (hright.sub hleft).eventually (eventually_gt_nhds (sub_pos.mpr hct))
  have hsmalllim : Tendsto (fun N : ℕ ↦ 2 * ((cap c N : ℝ) / N)) atTop (nhds 0) := by
    simpa only [mul_zero] using (cap_div_nat_tendsto c hc.le).const_mul 2
  have hsmall := hsmalllim.eventually (eventually_lt_nhds ha)
  have hcap := (cap_tendsto_atTop c hc).eventually (eventually_ge_atTop 1)
  filter_upwards [hpositive, hsmall, hcap, eventually_ge_atTop 2]
    with N hpositiveN hsmallN hcapN hN
  intro U B hbase hwidth
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hbudget_normalized :
      ((primeCount (cap c N) : ℝ) + 1 + t) * Real.log (64 * (cap c N : ℝ)) / Real.log N <
        Real.log (a * N) * griesmerFactor t / Real.log N := by
    change 0 < Real.log (a * N) * griesmerFactor t / Real.log N -
      (((primeCount (cap c N) : ℝ) + 1 + t) *
        Real.log (64 * (cap c N : ℝ)) / Real.log N) at hpositiveN
    linarith
  have hbudgetA : ((primeCount (cap c N) : ℝ) + 1 + t) *
      Real.log (64 * (cap c N : ℝ)) < Real.log (a * N) * griesmerFactor t :=
    (div_lt_div_iff_of_pos_right hlogN).mp hbudget_normalized
  have hlogbase : Real.log (a * N) ≤ Real.log U :=
    Real.log_le_log (mul_pos ha hNpos) hbase
  have hfactor : 0 < griesmerFactor t := hc.trans hct
  have hbudgetU := hbudgetA.trans_le (mul_le_mul_of_nonneg_right hlogbase hfactor.le)
  have htwo : (2 * (cap c N : ℝ)) / N < a := by
    simpa only [mul_div_assoc] using hsmallN
  have hcapU : 2 * cap c N ≤ U := by
    have h := ((div_lt_iff₀ hNpos).mp htwo).trans_le hbase
    exact_mod_cast h.le
  have hr := window_relation_finrank_lt_of_log_budget hcapN hcapU hbudgetU
  have hBcap : B ≤ cap c N := by
    have h : (B : ℝ) ≤ (cap c N : ℝ) := hwidth.trans (Nat.le_ceil _)
    exact_mod_cast h
  exact (window_relation_finrank_mono U hBcap).trans_lt hr

/-- The threshold is chosen before N, every base and every shorter window. -/
theorem uniform_relation_rank_lt (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (t : ℕ) (hct : c < griesmerFactor t) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ U B : ℕ,
      a * N ≤ (U : ℝ) → (B : ℝ) ≤ c * Real.log N →
        Module.finrank F₂ (windowRelationCode U B) < t :=
  eventually_atTop.mp (relation_rank_lt_eventually a c ha hc t hct)

/-- One lower base bound dominates every logarithmic window, independently
of the order parameter in the finite Griesmer inequality. -/
theorem base_dominates_windows_eventually (a D : ℝ) (ha : 0 < a) (hD : 0 ≤ D) :
    ∀ᶠ N : ℕ in atTop, ∀ U B : ℕ,
      a * N ≤ (U : ℝ) → (B : ℝ) ≤ D * Real.log N → 2 * B ≤ U := by
  have hlim : Tendsto (fun N : ℕ ↦ 2 * ((cap D N : ℝ) / N)) atTop (nhds 0) := by
    simpa only [mul_zero] using (cap_div_nat_tendsto D hD).const_mul 2
  filter_upwards [hlim.eventually (eventually_lt_nhds ha), eventually_ge_atTop 1]
    with N hsmall hN
  intro U B hbase hwidth
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have htwo : (2 * (cap D N : ℝ)) / N < a := by
    simpa only [mul_div_assoc] using hsmall
  have hcapU : 2 * cap D N ≤ U := by
    have h := ((div_lt_iff₀ hn).mp htwo).trans_le hbase
    exact_mod_cast h.le
  have hBcap : B ≤ cap D N := by
    have h : (B : ℝ) ≤ (cap D N : ℝ) := hwidth.trans (Nat.le_ceil _)
    exact_mod_cast h
  omega

/-- The exact finite displayed inequality in Lemma 2.1 holds uniformly in
all t, even when t varies with N. Only the later asymptotic rank conclusion
fixes t before N. -/
theorem finite_griesmer_eventually (a D : ℝ) (ha : 0 < a) (hD : 0 ≤ D) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ U B : ℕ,
      1 ≤ B → a * N ≤ (U : ℝ) → (B : ℝ) ≤ D * Real.log N →
        ∀ t : ℕ, t ≤ Module.finrank F₂ (windowRelationCode U B) →
          (∑ i ∈ Finset.range t,
            ⌈(LocalRigidityCode.rungeDistance U B : ℝ) / (2 : ℝ) ^ i⌉₊) - t ≤
              primeCount B + 1 := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (base_dominates_windows_eventually a D ha hD)
  exact ⟨N₀, fun N hN U B hB hbase hwidth t ht ↦
    window_relation_griesmer hB (hN₀ N hN U B hbase hwidth) ht⟩

theorem window_relation_finrank_zero_length (U : ℕ) :
    Module.finrank F₂ (windowRelationCode U 0) = 0 := by
  have h : Module.finrank F₂ (windowRelationCode U 0) ≤ 0 := by
    simpa only [Module.finrank_fin_fun] using (windowRelationCode U 0).finrank_le
  omega

/-- Uniform absence of even square relations for every subcritical length. -/
theorem uniform_subcritical_relation_rank_zero (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ U B : ℕ,
      a * N ≤ (U : ℝ) → (B : ℝ) ≤ (1 - ε) * Real.log N →
        Module.finrank F₂ (windowRelationCode U B) = 0 := by
  by_cases hsmall : ε < 1
  · obtain ⟨N₀, hN₀⟩ := uniform_relation_rank_lt a (1 - ε) ha (by linarith) 1
      (by simpa only [griesmerFactor_one] using (show 1 - ε < 1 by linarith))
    refine ⟨N₀, fun N hN U B hbase hwidth ↦ ?_⟩
    have h := hN₀ N hN U B hbase hwidth
    omega
  · refine ⟨2, fun N hN U B _hbase hwidth ↦ ?_⟩
    have hlog : 0 ≤ Real.log N :=
      (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).le
    have hnonpos : (1 - ε) * Real.log N ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
      (by linarith) hlog
    have hB0 : B = 0 := by
      have h : (B : ℝ) ≤ 0 := hwidth.trans hnonpos
      exact_mod_cast (le_antisymm h (Nat.cast_nonneg B))
    rw [hB0]
    exact window_relation_finrank_zero_length U

end PaperP1.UniformLocalRigidity
