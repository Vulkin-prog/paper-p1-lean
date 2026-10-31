module

public import PaperP1.Asymptotics.MomentObstructionLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # The actual moment-obstruction family and its subpolynomial distance

The large-N parameters are literal. For the finitely many invalid initial
indices both probability families use Poisson(1); this makes them globally
defined without changing any eventual statement.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MomentObstructionSequence

open Filter MeasureTheory Asymptotics PaperP1.MomentObstructionLog
  PaperP1.MomentObstructionMass PaperP1.MomentObstructionMoments PaperP1.MomentObstruction
open scoped Topology

def order (N : ℕ) : ℕ := ⌊Real.sqrt (Real.log N)⌋₊

def parameter (N : ℕ) : ℝ := Real.log N * (N : ℝ) ^ (-(2 / 3 : ℝ))

def Valid (N : ℕ) : Prop := 3 ≤ order N ∧ 0 ≤ parameter N ∧ parameter N ≤ 1

theorem log_nat_tendsto : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem sqrt_log_nat_tendsto : Tendsto (fun N : ℕ ↦ Real.sqrt (Real.log N)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp log_nat_tendsto

theorem order_tendsto : Tendsto order atTop atTop := by
  apply tendsto_atTop.mpr
  intro r
  have h := sqrt_log_nat_tendsto.eventually (eventually_ge_atTop (r : ℝ))
  exact h.mono fun N hN ↦ Nat.le_floor hN

theorem parameter_tendsto_zero : Tendsto parameter atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).tendsto_div_nhds_zero
  have hc := h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply hc.congr'
  exact Filter.Eventually.of_forall fun N ↦ by
    simp only [parameter, Real.rpow_neg (Nat.cast_nonneg N), div_eq_mul_inv, Function.comp_apply]

theorem parameter_nonneg (N : ℕ) : 0 ≤ parameter N := by
  cases N with
  | zero => norm_num [parameter]
  | succ N =>
    apply mul_nonneg
    · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + 1 by omega))
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem valid_eventually : ∀ᶠ N : ℕ in atTop, Valid N := by
  have ha := parameter_tendsto_zero.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [order_tendsto.eventually (eventually_ge_atTop 3), ha] with N hm ha
  exact ⟨hm, parameter_nonneg N, ha.le⟩

def familyLaw (N : ℕ) : ProbabilityMeasure ℕ := by
  classical
  exact if hN : Valid N then
    pLaw (order N) (by have h := hN.1; omega) (parameter N) hN.2.1 (by have h := hN.2.2; linarith)
  else qLaw 0 (by norm_num) (by norm_num)

def referenceFamily (N : ℕ) : ProbabilityMeasure ℕ := by
  classical
  exact if hN : Valid N then qLaw (parameter N) hN.2.1 (by have h := hN.2.2; linarith)
  else qLaw 0 (by norm_num) (by norm_num)

def familyDistance (N : ℕ) : ℝ := AtomicProbability.totalVariation (familyLaw N) (referenceFamily N)

theorem familyDistance_eq (N : ℕ) (hN : Valid N) : familyDistance N = distance (order N) (parameter N) := by
  rw [familyDistance, familyLaw, referenceFamily, dite_eq_left hN, dite_eq_left hN]
  exact totalVariation_exact _ _ (by have h := hN.1; omega) _ _ _

theorem fixed_factorial_moments_eventually (r : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (∫ k : ℕ, (k.descFactorial r : ℝ) ∂(familyLaw N : Measure ℕ)) =
        1 + (r.choose 2 : ℝ) * parameter N := by
  filter_upwards [valid_eventually, order_tendsto.eventually (eventually_gt_atTop r)] with N hN hr
  rw [familyLaw, dite_eq_left hN]
  exact pLaw_factorial_moment_of_ne _ _ _ _ _ _ (ne_of_lt hr)

theorem exponential_bound_eventually (t : ℝ) :
    ∀ᶠ N : ℕ in atTop, Integrable (fun k : ℕ ↦ Real.exp (t * k)) (familyLaw N : Measure ℕ) ∧
      (∫ k : ℕ, Real.exp (t * k) ∂(familyLaw N : Measure ℕ)) ≤
        3 / 2 * Real.exp (Real.exp t - 1) * (1 + (1 / 2) * (Real.exp t - 1) ^ 2) := by
  filter_upwards [valid_eventually] with N hN
  rw [familyLaw, dite_eq_left hN]
  exact companion_T23_1_exponential _ hN.1 _ hN.2.1 hN.2.2 t

theorem log_distance_error_isBigO :
    (fun N : ℕ ↦ Real.log (familyDistance N) +
      (1 / 2) * Real.sqrt (Real.log N) * Real.log (Real.log N)) =O[atTop]
        (fun N : ℕ ↦ Real.sqrt (Real.log N)) := by
  apply Asymptotics.IsBigO.of_bound 3
  filter_upwards [valid_eventually, log_nat_tendsto.eventually (eventually_ge_atTop 9)] with N hN hlog
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), familyDistance_eq N hN]
  exact log_distance_sqrt_log_bound N hlog _ hN.2.1 hN.2.2

theorem log_sqrt_budget (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ z : ℝ in atTop, 9 ≤ z ∧ (1 / 2) * Real.log z + 3 < γ * Real.sqrt z := by
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).def hγ
  have hsqrt := Real.tendsto_sqrt_atTop.eventually (eventually_gt_atTop (6 / γ))
  filter_upwards [hlog, hsqrt, eventually_ge_atTop 9] with z hlog hsqrt hz
  have hz0 : 0 ≤ z := by linarith
  have hl0 : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg hl0, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hz0 _), ← Real.sqrt_eq_rpow] at hlog
  have hs : 6 < Real.sqrt z * γ := (div_lt_iff₀ hγ).mp hsqrt
  exact ⟨hz, by nlinarith⟩

theorem uniform_distance_exceeds_power (γ : ℝ) (hγ : 0 < γ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      (N : ℝ) ^ (-γ) < distance (order N) a := by
  have hbudget := log_nat_tendsto.eventually (log_sqrt_budget γ hγ)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hbudget.and (eventually_ge_atTop 2))
  refine ⟨N₀, ?_⟩
  intro N hN a ha0 ha1
  obtain ⟨⟨hlog, hbudget⟩, hNtwo⟩ := hN₀ N hN
  have hlog0 : 0 ≤ Real.log N := by linarith
  have hx : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr (by linarith)
  have herr := abs_le.mp (log_distance_sqrt_log_bound N hlog a ha0 ha1)
  have hsquare := Real.sq_sqrt hlog0
  have hmul := mul_lt_mul_of_pos_right hbudget hx
  have hlogdistance : -γ * Real.log N < Real.log (distance (order N) a) := by
    dsimp [order]
    nlinarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ = Real.exp (-γ * Real.log N) := by rw [Real.rpow_def_of_pos hNpos]; congr 1; ring
    _ < Real.exp (Real.log (distance (order N) a)) := Real.exp_lt_exp.mpr hlogdistance
    _ = _ := Real.exp_log (distance_pos _ a ha1)

theorem distance_exceeds_every_power (γ : ℝ) (hγ : 0 < γ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, (N : ℝ) ^ (-γ) < familyDistance N := by
  obtain ⟨N₁, hN₁⟩ := uniform_distance_exceeds_power γ hγ
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp valid_eventually
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN
  have hv := hN₂ N ((le_max_right _ _).trans hN)
  rw [familyDistance_eq N hv]
  exact hN₁ N ((le_max_left _ _).trans hN) _ hv.2.1 hv.2.2

end PaperP1.MomentObstructionSequence
