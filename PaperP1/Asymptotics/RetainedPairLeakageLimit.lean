module

public import PaperP1.Asymptotics.RetainedPairLeakage
public import PaperP1.Analysis.WeightedLeakageCutoff

/-! # Internal actual exceptional-event bounds prove the complete weighted pair leakage is uniformly little-o of the pair scale -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedPairLeakageLimit

open Finset Filter PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.RegularStarts
  PaperP1.RetainedActiveSubsetMoments PaperP1.RetainedPairMomentGenerator PaperP1.RetainedExceptionalEvent

theorem uniform_relative (C : ℝ) :
    ∀ η : ℝ, 0 < η →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        (∑' r : ℕ, (2 : ℝ) ^ r * pairLeakage (8 * (L + 1) : ℕ) N L r) ≤ η * SecondFactorialCorrection.value N L := by
  classical
  have hp := RetainedPairLeakage.uniform_fixed_pair C
  obtain ⟨A, hA, NA, _hNA, ha⟩ := RetainedPairLeakage.uniform_generator_bound C
  obtain ⟨c, hc, NC, _hNC, hcl⟩ := SecondFactorialCorrectionLower.uniform_lower C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  intro η hη
  have hpow : Tendsto (fun j : ℕ ↦ (2 : ℝ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hpow.eventually (eventually_ge_atTop (2 * A / η)))
  let B : ℝ := ∑ r ∈ range (J + 1), (2 : ℝ) ^ r
  have hper (i : Fin (J + 1)) := hp i.val
  choose Nt _hNt ht using hper
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 * B / (η * c)) (-83 / 120) (1 / 40) (by norm_num)
  refine ⟨10 + NA + NC + NG + NF + univ.sup Nt, by omega, ?_⟩
  intro N hN L hband
  let H : ℝ := (8 * (L + 1) : ℕ)
  let a := SecondFactorialCorrection.value N L
  have hnpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : (1 : ℝ) ≤ L := by
    have h := (hg N (by omega) L hband).2.2.1
    exact_mod_cast (show 1 ≤ L by omega)
  have hlower : c * (N : ℝ) ^ (-2 / 3 : ℝ) ≤ a := by
    calc
      _ ≤ c * L * (N : ℝ) ^ (-2 / 3 : ℝ) := by
        have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL hc.le)
          (Real.rpow_nonneg hnpos.le (-2 / 3 : ℝ))
        simpa only [mul_one] using h
      _ ≤ _ := hcl N (by omega) L hband
  have ha0 : 0 ≤ a := (mul_nonneg hc.le (Real.rpow_nonneg hnpos.le _)).trans hlower
  have hcoeff : ((2 : ℝ) ^ J)⁻¹ * A ≤ η / 2 := by
    rw [mul_comm, ← div_eq_mul_inv]
    apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) J)).mpr
    have h := (div_le_iff₀ hη).mp (hJ J le_rfl)
    linarith only [h]
  have hlowraw : (∑ r ∈ range (J + 1), (2 : ℝ) ^ r * pairLeakage H N L r) ≤ B * (N : ℝ) ^ (-83 / 120 : ℝ) := by
    dsimp only [B]
    rw [sum_mul]
    apply sum_le_sum
    intro r hr
    let i : Fin (J + 1) := ⟨r, mem_range.mp hr⟩
    have hNi : Nt i ≤ univ.sup Nt := le_sup (f := Nt) (mem_univ i)
    exact mul_le_mul_of_nonneg_left (ht i N (by omega) L hband) (by positivity)
  have hlow : (∑ r ∈ range (J + 1), (2 : ℝ) ^ r * pairLeakage H N L r) ≤ (η / 2) * a := by
    have hfactor := hf N (by omega)
    norm_num only [show (-83 / 120 : ℝ) + 1 / 40 = -2 / 3 by norm_num] at hfactor
    have hscaled := mul_le_mul_of_nonneg_left hfactor (by positivity : 0 ≤ η / 2 * c)
    have heq : (η / 2 * c) * (2 * B / (η * c)) = B := by field_simp
    rw [← mul_assoc, heq] at hscaled
    have hlast := mul_le_mul_of_nonneg_left hlower (by positivity : 0 ≤ η / 2)
    nlinarith only [hlowraw, hscaled, hlast]
  have hgen : leakageSum 4 H N L ≤ A * a := ha N (by omega) L hband H
  have htail : ((2 : ℝ) ^ J)⁻¹ * leakageSum 4 H N L ≤ (η / 2) * a := by
    calc
      _ ≤ ((2 : ℝ) ^ J)⁻¹ * (A * a) := mul_le_mul_of_nonneg_left hgen (by positivity)
      _ = (((2 : ℝ) ^ J)⁻¹ * A) * a := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff ha0
  have hsplit := WeightedLeakageCutoff.finite_split (fun r ↦ pairLeakage H N L r)
    (RetainedModifiedMomentDecomposition.pairLeakage_nonneg H N L) (regularStarts N L).card J
  rw [← leakageSum_eq_tsum]
  change leakageSum 2 H N L ≤ η * a
  change leakageSum 2 H N L ≤ (∑ r ∈ range (J + 1), (2 : ℝ) ^ r * pairLeakage H N L r) +
    ((2 : ℝ) ^ J)⁻¹ * leakageSum 4 H N L at hsplit
  linarith only [hsplit, hlow, htail]

end PaperP1.RetainedPairLeakageLimit
