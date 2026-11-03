module

public import PaperP1.Asymptotics.UniformGraphCardinalityTail

/-! # Independent graph tails with separate marked and degree exponents -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformGraphExponentTail

open Finset PaperP1.GraphStarWeights PaperP1.MarkedGraphGenerator

theorem uniform_tail (M d q γ ε : ℝ) (hM : 0 ≤ M) (hγ : 0 < γ)
    (hmarkgap : d + γ ≤ 1) (hstargap : q + 2 * γ < 1) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (Fintype.card V : ℝ) ≤ N → ∀ marks : Finset V,
      (marks.card : ℝ) ≤ (N : ℝ) ^ d → (G.maxDegree : ℝ) ≤ (N : ℝ) ^ q →
      ∀ s : ℕ, ∀ F : Finset (Finset V), F ⊆ families G marks → (∀ D ∈ F, s ≤ D.card) →
      (∑ D ∈ F, (M / N) ^ D.card) ≤ (N : ℝ) ^ (-γ * s + ε) := by
  have hgap : 0 < 1 - q - γ := by linarith only [hstargap, hγ]
  obtain ⟨NS, hs⟩ := PaperP1.HalfCountSchedule.factor_absorption (8 * M) 0 (1 - q - γ) hgap
  obtain ⟨NK, hk⟩ := PaperP1.HalfCountSchedule.factor_absorption
    (Real.exp (M + 8 * M ^ 2)) 0 ε hε
  refine ⟨max 2 (max NS NK), by omega, ?_⟩
  intro N hN V _ _ G _ hV marks hm hD s F hF hcard
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hscale : 8 * M ≤ (N : ℝ) ^ (1 - q - γ) := by
    simpa only [Real.rpow_zero, mul_one, zero_add] using hs N (by omega)
  have hconstant : Real.exp (M + 8 * M ^ 2) ≤ (N : ℝ) ^ ε := by
    simpa only [Real.rpow_zero, mul_one, zero_add] using hk N (by omega)
  let z := M * (N : ℝ) ^ (-1 + γ)
  have hz : 0 ≤ z := mul_nonneg hM (Real.rpow_nonneg hn.le _)
  have hprod : (N : ℝ) ^ q * z = M * (N : ℝ) ^ (-(1 - q - γ)) := by
    dsimp [z]
    rw [mul_left_comm, ← Real.rpow_add hn]
    congr 1
    congr 1
    ring
  have hsmall : (G.maxDegree : ℝ) * z ≤ 1 / 8 := by
    calc
      _ ≤ (N : ℝ) ^ q * z := mul_le_mul_of_nonneg_right hD hz
      _ = M / (N : ℝ) ^ (1 - q - γ) := by
        rw [hprod, Real.rpow_neg hn.le, div_eq_mul_inv]
      _ ≤ _ := (div_le_iff₀ (Real.rpow_pos_of_pos hn _)).mpr (by linarith only [hscale])
  have hmark : (marks.card : ℝ) * z ≤ M := by
    have hpow : (N : ℝ) ^ (d - 1 + γ) ≤ 1 := by
      simpa only [Real.rpow_zero] using
        (Real.rpow_le_rpow_of_exponent_le hn1
          (show d - 1 + γ ≤ 0 by linarith only [hmarkgap]))
    calc
      _ ≤ (N : ℝ) ^ d * z := mul_le_mul_of_nonneg_right hm hz
      _ = M * (N : ℝ) ^ (d - 1 + γ) := by
        dsimp [z]
        rw [mul_left_comm, ← Real.rpow_add hn]
        congr 1
        congr 1
        ring
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left hpow hM
      _ = _ := mul_one _
  have hzsquare : z ^ 2 = M ^ 2 * (N : ℝ) ^ (2 * (-1 + γ)) := by
    dsimp [z]
    rw [mul_pow, ← Real.rpow_mul_natCast hn.le]
    congr 1
    congr 1
    ring
  have hstar : (Fintype.card V : ℝ) * G.maxDegree * z ^ 2 ≤ M ^ 2 := by
    have hpow : (N : ℝ) ^ (1 + q + 2 * (-1 + γ)) ≤ 1 := by
      simpa only [Real.rpow_zero] using
        (Real.rpow_le_rpow_of_exponent_le hn1
          (show 1 + q + 2 * (-1 + γ) ≤ 0 by linarith only [hstargap]))
    calc
      _ ≤ (N : ℝ) * (N : ℝ) ^ q * z ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul hV hD (Nat.cast_nonneg _) hn.le) (sq_nonneg z)
      _ = M ^ 2 * (N : ℝ) ^ (1 + q + 2 * (-1 + γ)) := by
        rw [hzsquare, Real.rpow_add hn, Real.rpow_add hn, Real.rpow_one]
        ring
      _ ≤ M ^ 2 * 1 := mul_le_mul_of_nonneg_left hpow (sq_nonneg M)
      _ = _ := mul_one _
  have htotal := PaperP1.PowerTiltedGraphTail.total_bound G marks z M hz hmark hstar hsmall
  have hzEq : M / N * (N : ℝ) ^ γ = z := by
    dsimp [z]
    rw [Real.rpow_add hn, Real.rpow_neg_one]
    ring
  have htilt := PaperP1.PowerTiltedGraphTail.tilt_bound G marks F s hF hcard
    (M / N) ((N : ℝ) ^ γ) (div_nonneg hM hn.le) (Real.one_le_rpow hn1 hγ.le)
  rw [hzEq] at htilt
  have hbound : (∑ D ∈ F, (M / N) ^ D.card) ≤
      Real.exp (M + 8 * M ^ 2) / ((N : ℝ) ^ γ) ^ s := by
    apply (le_div_iff₀ (pow_pos (Real.rpow_pos_of_pos hn _) _)).mpr
    exact (mul_comm _ _).trans_le (htilt.trans htotal)
  calc
    _ ≤ Real.exp (M + 8 * M ^ 2) / (N : ℝ) ^ (γ * (s : ℝ)) := by
      simpa only [Real.rpow_mul_natCast hn.le] using hbound
    _ ≤ (N : ℝ) ^ ε / (N : ℝ) ^ (γ * (s : ℝ)) :=
      div_le_div_of_nonneg_right hconstant (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_sub hn]; congr 1; ring

end PaperP1.UniformGraphExponentTail
