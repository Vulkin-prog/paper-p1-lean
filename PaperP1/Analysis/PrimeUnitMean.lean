module

public import PaperP1.Analysis.WeightedPrimeMean
public import Mathlib.Topology.Order.Compact

/-! # Translated prime means and actual local-square frequency budgets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeUnitMean
open Finset MeasureTheory PaperP1 GaussianExponentialSums LogarithmicPhase WeightedPrimeMean
open scoped Classical

def shifted (a : ℕ → ℂ) (h : ℝ) (p : ℕ) : ℂ := a p*phase (-Real.log (p : ℝ)) h

def energy (P : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ p ∈ P, (Real.log (p : ℝ)/(p : ℝ))*‖a p‖^2

def localSquareSup (F : ℝ → ℂ) (h : ℝ) : ℝ :=
  sSup ((fun t ↦ ‖F t‖^2) '' Set.Icc (h-1/2) (h+1/2))

theorem phase_time_add (w t h : ℝ) : phase w (t+h)=phase w t*phase w h := by
  unfold phase
  rw [Complex.ofReal_add,mul_add,Complex.exp_add]

theorem value_add (P : Finset ℕ) (a : ℕ → ℂ) (t h : ℝ) :
    value P a (t+h)=value P (shifted a h) t := by
  unfold value polynomial shifted
  apply sum_congr rfl
  intro p hp
  rw [phase_time_add]
  ring

theorem energy_shifted (P : Finset ℕ) (a : ℕ → ℂ) (h : ℝ) :
    energy P (shifted a h)=energy P a := by
  simp only [energy,shifted,norm_mul,phase_norm,mul_one]

theorem shifted_mean (P : Finset ℕ) (a : ℕ → ℂ) (T h : ℝ) (hT : 1 ≤ T)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ T^2 ≤ (p : ℝ)) :
    (∫ t in h-T..h+T, ‖value P a t‖^2) ≤ WeightedPrimeMean.constant*energy P a := by
  have he : (∫ t in -T..T, ‖value P a (t+h)‖^2)=(∫ t in h-T..h+T, ‖value P a t‖^2) := by
    have hh := intervalIntegral.integral_comp_add_right (a := -T) (b := T)
      (fun t : ℝ ↦ ‖value P a t‖^2) h
    simpa only [sub_eq_add_neg,add_comm] using hh
  have hh := WeightedPrimeMean.mean_square P (shifted a h) T hT hP
  change (∫ t in -T..T, ‖value P (shifted a h) t‖^2) ≤ WeightedPrimeMean.constant*energy P (shifted a h) at hh
  rw [energy_shifted] at hh
  simp_rw [← value_add] at hh
  rwa [he] at hh

theorem unit_mean (P : Finset ℕ) (a : ℕ → ℂ) (h : ℝ)
    (hP : ∀ p ∈ P, Nat.Prime p) :
    (∫ t in h-1/2..h+1/2, ‖value P a t‖^2) ≤ WeightedPrimeMean.constant*energy P a := by
  have hc := (value_continuous P a).norm.pow 2
  have hm : (∫ t in h-1/2..h+1/2, ‖value P a t‖^2) ≤
      ∫ t in h-1..h+1, ‖value P a t‖^2 := by
    apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _)) (hc.intervalIntegrable _ _)
  exact hm.trans (shifted_mean P a 1 h (by norm_num) (by
    intro p hp
    exact ⟨hP p hp,by norm_num; exact_mod_cast (hP p hp).one_le⟩))

theorem local_sup_attained (F : ℝ → ℂ) (hF : Continuous F) (h : ℝ) :
    ∃ t ∈ Set.Icc (h-1/2) (h+1/2), localSquareSup F h=‖F t‖^2 := by
  exact isCompact_Icc.exists_sSup_image_eq (Set.nonempty_Icc.mpr (by linarith)) (hF.norm.pow 2).continuousOn

theorem local_sup_nonneg (F : ℝ → ℂ) (hF : Continuous F) (h : ℝ) : 0 ≤ localSquareSup F h := by
  obtain ⟨t,ht,he⟩ := local_sup_attained F hF h
  rw [he]
  exact sq_nonneg _

theorem norm_sq_le_local_sup (F : ℝ → ℂ) (hF : Continuous F) (h t : ℝ)
    (ht : t ∈ Set.Icc (h-1/2) (h+1/2)) : ‖F t‖^2 ≤ localSquareSup F h := by
  exact (hF.norm.pow 2).continuousOn.le_sSup_image_Icc ht

def frequencyBudget (F : ℝ → ℂ) (K : ℕ) : ℝ :=
  ∑ j ∈ range (2*K+1), localSquareSup F ((j : ℝ)-(K : ℝ))/(1+((j : ℝ)-(K : ℝ))^2)

theorem energy_nonneg (P : Finset ℕ) (a : ℕ → ℂ) : 0 ≤ energy P a := by
  apply sum_nonneg
  intro p hp
  exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)) (sq_nonneg _)

theorem inverse_weight_comparison (h t : ℝ) (ht : t ∈ Set.Icc (h-1/2) (h+1/2)) :
    1/(1+t^2) ≤ 2/(1+h^2) := by
  have hdiff : (h-t)^2 ≤ (1/4 : ℝ) := by nlinarith [ht.1,ht.2]
  have hh : 1+h^2 ≤ 2*(1+t^2) := by nlinarith [sq_nonneg (h-2*t)]
  exact (div_le_div_iff₀ (by positivity : 0 < 1+t^2) (by positivity : 0 < 1+h^2)).mpr (by simpa only [one_mul] using hh)

theorem unit_weighted_mean (P : Finset ℕ) (a : ℕ → ℂ) (F : ℝ → ℂ) (hF : Continuous F)
    (h : ℝ) (hP : ∀ p ∈ P, Nat.Prime p) :
    (∫ t in h-1/2..h+1/2, ‖value P a t‖^2*‖F t‖^2/(1+t^2)) ≤
      2*WeightedPrimeMean.constant*energy P a*localSquareSup F h/(1+h^2) := by
  have hg : Continuous (fun t : ℝ ↦ ‖value P a t‖^2*‖F t‖^2/(1+t^2)) := by
    apply Continuous.div ((value_continuous P a).norm.pow 2 |>.mul (hF.norm.pow 2))
      (continuous_const.add (continuous_id.pow 2))
    intro t
    change (1+t^2 : ℝ) ≠ 0
    positivity
  have hc := (value_continuous P a).norm.pow 2
  have hsup := local_sup_nonneg F hF h
  have hpref : 0 ≤ 2*localSquareSup F h/(1+h^2) := by positivity
  calc
    _ ≤ ∫ t in h-1/2..h+1/2, (2*localSquareSup F h/(1+h^2))*‖value P a t‖^2 := by
      apply intervalIntegral.integral_mono_on (by linarith) (hg.intervalIntegrable _ _)
        ((continuous_const.mul hc).intervalIntegrable _ _)
      intro t ht
      have hb := norm_sq_le_local_sup F hF h t ht
      have hw := inverse_weight_comparison h t ht
      have hm : ‖F t‖^2/(1+t^2) ≤ 2*localSquareSup F h/(1+h^2) := by
        calc
          _ ≤ localSquareSup F h/(1+t^2) := div_le_div_of_nonneg_right hb (by positivity)
          _ = localSquareSup F h*(1/(1+t^2)) := by ring
          _ ≤ localSquareSup F h*(2/(1+h^2)) := mul_le_mul_of_nonneg_left hw hsup
          _ = _ := by ring
      have hh := mul_le_mul_of_nonneg_left hm (sq_nonneg ‖value P a t‖)
      calc
        _ = ‖value P a t‖^2*(‖F t‖^2/(1+t^2)) := by ring
        _ ≤ ‖value P a t‖^2*(2*localSquareSup F h/(1+h^2)) := hh
        _ = _ := by simp only [Pi.mul_apply,Pi.pow_apply]; ring
    _ = (2*localSquareSup F h/(1+h^2))*(∫ t in h-1/2..h+1/2, ‖value P a t‖^2) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (2*localSquareSup F h/(1+h^2))*(WeightedPrimeMean.constant*energy P a) :=
      mul_le_mul_of_nonneg_left (unit_mean P a h hP) hpref
    _ = _ := by ring

theorem unit_integrals_cover (g : ℝ → ℝ) (hg : Continuous g) (K : ℕ) :
    (∑ j ∈ range (2*K+1), ∫ t in (j : ℝ)-(K : ℝ)-1/2..(j : ℝ)-(K : ℝ)+1/2, g t)=
      ∫ t in -(K : ℝ)-1/2..(K : ℝ)+1/2, g t := by
  let ep : ℕ → ℝ := fun j ↦ (j : ℝ)-(K : ℝ)-1/2
  have hh := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := g) (a := ep) (n := 2*K+1)
    (fun j hj ↦ hg.intervalIntegrable (ep j) (ep (j+1)))
  have hlo : ep 0=-(K : ℝ)-1/2 := by simp [ep]
  have hhi : ep (2*K+1)=(K : ℝ)+1/2 := by dsimp only [ep]; push_cast; ring
  rw [hlo,hhi] at hh
  rw [← hh]
  apply sum_congr rfl
  intro j hj
  have he : ep (j+1)=(j : ℝ)-(K : ℝ)+1/2 := by dsimp only [ep]; push_cast; ring
  rw [he]

theorem frequency_budget_mean (P : Finset ℕ) (a : ℕ → ℂ) (F : ℝ → ℂ) (hF : Continuous F)
    (K : ℕ) (T : ℝ) (hT : 0 < T) (hTK : T ≤ (K : ℝ)+1/2)
    (hP : ∀ p ∈ P, Nat.Prime p) :
    (∫ t in -T..T, ‖value P a t‖^2*‖F t‖^2/(1+t^2)) ≤
      2*WeightedPrimeMean.constant*energy P a*frequencyBudget F K := by
  let g : ℝ → ℝ := fun t ↦ ‖value P a t‖^2*‖F t‖^2/(1+t^2)
  have hg : Continuous g := by
    apply Continuous.div ((value_continuous P a).norm.pow 2 |>.mul (hF.norm.pow 2))
      (continuous_const.add (continuous_id.pow 2))
    intro t
    change (1+t^2 : ℝ) ≠ 0
    positivity
  have hnonneg (t : ℝ) : 0 ≤ g t := by dsimp only [g]; positivity
  calc
    _ ≤ ∫ t in -(K : ℝ)-1/2..(K : ℝ)+1/2, g t := by
      apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) hTK
        (Filter.Eventually.of_forall hnonneg) (hg.intervalIntegrable _ _)
    _ = ∑ j ∈ range (2*K+1), ∫ t in (j : ℝ)-(K : ℝ)-1/2..(j : ℝ)-(K : ℝ)+1/2, g t :=
      (unit_integrals_cover g hg K).symm
    _ ≤ ∑ j ∈ range (2*K+1),
        2*WeightedPrimeMean.constant*energy P a*localSquareSup F ((j : ℝ)-(K : ℝ))/(1+((j : ℝ)-(K : ℝ))^2) :=
      sum_le_sum (fun j hj ↦ unit_weighted_mean P a F hF ((j : ℝ)-(K : ℝ)) hP)
    _ = _ := by
      rw [frequencyBudget,mul_sum]
      apply sum_congr rfl
      intro j hj
      ring

theorem frequency_budget_nonneg (F : ℝ → ℂ) (hF : Continuous F) (K : ℕ) :
    0 ≤ frequencyBudget F K := by
  apply sum_nonneg
  intro j hj
  exact div_nonneg (local_sup_nonneg F hF _) (by positivity)
end PaperP1.PrimeUnitMean


