module

public import PaperP1.Analysis.DeterminantTwoKernelExponents
public import PaperP1.Analysis.DeterminantBoxScales
public import PaperP1.Arithmetic.DeterminantSourceBox
public import Mathlib.Analysis.Real.Sqrt

/-! # Apply the exact seven-twelfths optimization to the literal source-box costs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantSevenTwelfthsCosts

open PaperP1.DeterminantSourceBox PaperP1.DeterminantLogScale PaperP1.DeterminantTwoKernelExponents

theorem sqrt_exp_as_power (N P F r : ℝ) (hN : 0 < N) (hP : 0 < P)
    (hlog : Real.log P + F = 2 * r * Real.log N) : Real.sqrt (P * Real.exp F) = N ^ r := by
  have hp : 0 < P * Real.exp F := mul_pos hP (Real.exp_pos F)
  have hl : Real.log (Real.sqrt (P * Real.exp F)) = r * Real.log N := by
    rw [Real.log_sqrt hp.le, Real.log_mul hP.ne' (Real.exp_pos F).ne', Real.log_exp]
    linarith only [hlog]
  calc
    _ = Real.exp (Real.log (Real.sqrt (P * Real.exp F))) := (Real.exp_log (Real.sqrt_pos.mpr hp)).symm
    _ = Real.exp (r * Real.log N) := congrArg Real.exp hl
    _ = _ := by rw [Real.rpow_def_of_pos hN]; congr 1; ring

theorem root_identities (N D E U V : ℝ) (hN : 1 < N) (hD : 0 < D) (hE : 0 < E) (hU : 0 < U) (hV : 0 < V) :
    let z := Real.log (D * E) / Real.log N
    let w := z + Real.log (U * V) / (2 * Real.log N)
    Real.sqrt (D * E * Real.exp (logShape N D E U V)) = N ^ first z w ∧
      Real.sqrt (U * V * Real.exp (logShape N D E U V)) = N ^ second z w := by
  have ht : Real.log N ≠ 0 := (Real.log_pos hN).ne'
  constructor
  · apply sqrt_exp_as_power N (D * E) (logShape N D E U V) _ (by linarith) (mul_pos hD hE)
    dsimp only [first, logShape]
    field_simp
    ring
  · apply sqrt_exp_as_power N (U * V) (logShape N D E U V) _ (by linarith) (mul_pos hU hV)
    dsimp only [second, logShape]
    field_simp
    ring

theorem uniform_root_minimum (C η : ℝ) (hC : 0 < C) (hη : 0 < η) (hηsmall : η ≤ 1 / 3) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ρ δ : ℝ, ∀ X : Box N ρ C δ,
      min (Real.sqrt (X.D * X.E * Real.exp (logShape N X.D X.E X.U X.V)))
        (Real.sqrt (X.U * X.V * Real.exp (logShape N X.D X.E X.U X.V))) ≤ (N : ℝ) ^ (7 / 12 + η) := by
  obtain ⟨N₀, hN₀⟩ := DeterminantNormalizedWeights.fixed_log_error C η hη
  refine ⟨max 2 N₀, ?_⟩
  intro N hN ρ δ X
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have ht : 0 < Real.log (N : ℝ) := Real.log_pos hn
  obtain ⟨_hn₂, hlogC⟩ := hN₀ N (by omega)
  have hcoeff : 1 ≤ X.c₁ * X.c₂ := by
    nlinarith only [X.c₁_ge_one, X.c₂_ge_one, mul_nonneg (sub_nonneg.mpr X.c₁_ge_one) (sub_nonneg.mpr X.c₂_ge_one)]
  have hD : 0 < X.D := by linarith [X.D_ge_one]
  have hE : 0 < X.E := by linarith [X.E_ge_one]
  have hU : 0 < X.U := by linarith [X.U_ge_one]
  have hV : 0 < X.V := by linarith [X.V_ge_one]
  have hA : 0 ≤ Real.log (X.D * X.E) := by
    apply Real.log_nonneg
    nlinarith only [X.D_ge_one, X.E_ge_one, mul_nonneg (sub_nonneg.mpr X.D_ge_one) (sub_nonneg.mpr X.E_ge_one)]
  have hB : 0 ≤ Real.log (X.U * X.V) := by
    apply Real.log_nonneg
    nlinarith only [X.U_ge_one, X.V_ge_one, mul_nonneg (sub_nonneg.mpr X.U_ge_one) (sub_nonneg.mpr X.V_ge_one)]
  let z := Real.log (X.D * X.E) / Real.log N
  let w := z + Real.log (X.U * X.V) / (2 * Real.log N)
  have hw : 0 ≤ w := by dsimp only [w, z]; positivity
  have huv := log_parameter_upper (by linarith : (0 : ℝ) < N) hC
    (by linarith [X.c₁_ge_one]) (by linarith [X.c₂_ge_one]) hD hE hU hV hcoeff X.first_upper X.second_upper
  have hwt : w * Real.log N = Real.log (X.D * X.E) + Real.log (X.U * X.V) / 2 := by
    dsimp only [w, z]
    field_simp
  have hlogCup : Real.log C ≤ η * Real.log N := (div_le_iff₀ ht).mp hlogC
  have hwup : w ≤ 1 + η := by
    apply (mul_le_mul_iff_of_pos_right ht).mp
    nlinarith only [hwt, huv, hlogCup]
  obtain ⟨hid₁, hid₂⟩ := root_identities N X.D X.E X.U X.V hn hD hE hU hV
  rw [hid₁, hid₂]
  exact min_power_bound hn.le z w η hη.le hηsmall hw hwup

theorem uniform_complete_cost (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ ρ δ : ℝ, ∀ X : Box N ρ C δ, ∀ T : ℝ, 0 ≤ T → X.U ≤ T → X.V ≤ T →
      min (Real.sqrt (X.D * X.E * Real.exp (logShape N X.D X.E X.U X.V)) + X.D + X.E)
        (Real.sqrt (X.U * X.V * Real.exp (logShape N X.D X.E X.U X.V)) + X.U + X.V) ≤
          (T + (N : ℝ) ^ (7 / 12 : ℝ)) * (N : ℝ) ^ ε := by
  let η := min (ε / 2) (1 / 3 : ℝ)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  obtain ⟨Nr, hr⟩ := uniform_root_minimum C η hC hη (min_le_right _ _)
  let B := 3 + 2 * Real.sqrt C
  obtain ⟨Nk, hk⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow B 0 (ε / 2) (by positivity)
  refine ⟨max 2 (max Nr Nk), ?_⟩
  intro N hN ρ δ X T hT hU hV
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn₁ : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let R := (N : ℝ) ^ (7 / 12 : ℝ)
  let p := (N : ℝ) ^ (ε / 2)
  let a := Real.sqrt (X.D * X.E * Real.exp (logShape N X.D X.E X.U X.V))
  let b := Real.sqrt (X.U * X.V * Real.exp (logShape N X.D X.E X.U X.V))
  have hR : 0 ≤ R := Real.rpow_nonneg hn.le _
  have hp : 1 ≤ p := Real.one_le_rpow hn₁ (by positivity)
  have hp₀ : 0 ≤ p := by linarith
  have hroot : min a b ≤ p * R := by
    calc
      _ ≤ (N : ℝ) ^ (7 / 12 + η) := hr N (by omega) ρ δ X
      _ ≤ (N : ℝ) ^ (ε / 2 + 7 / 12) :=
        Real.rpow_le_rpow_of_exponent_le hn₁ (by linarith only [min_le_left (ε / 2) (1 / 3 : ℝ)])
      _ = _ := Real.rpow_add hn _ _
  have hD₀ : 0 ≤ X.D := by linarith [X.D_ge_one]
  have hE₀ : 0 ≤ X.E := by linarith [X.E_ge_one]
  have hU₀ : 0 ≤ X.U := by linarith [X.U_ge_one]
  have hV₀ : 0 ≤ X.V := by linarith [X.V_ge_one]
  have hd : X.D ≤ Real.sqrt C * Real.sqrt N := by
    have hsq := (DeterminantBoxScales.coordinate_bounds X.c₁_ge_one X.D_ge_one X.U_ge_one X.first_upper).1
    have hb := Real.le_sqrt_of_sq_le hsq
    simpa only [Real.sqrt_mul hC.le] using hb
  have he : X.E ≤ Real.sqrt C * Real.sqrt N := by
    have hsq := (DeterminantBoxScales.coordinate_bounds X.c₂_ge_one X.E_ge_one X.V_ge_one X.second_upper).1
    have hb := Real.le_sqrt_of_sq_le hsq
    simpa only [Real.sqrt_mul hC.le] using hb
  have hsmall : Real.sqrt (N : ℝ) ≤ R := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hn₁ (by norm_num : (1 / 2 : ℝ) ≤ 7 / 12)
  have haxes : X.D + X.E + X.U + X.V ≤ 2 * Real.sqrt C * R + 2 * T := by
    have ht := mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg C)
    linarith only [hd, he, ht, hU, hV]
  have hmin : min (a + X.D + X.E) (b + X.U + X.V) ≤ min a b + X.D + X.E + X.U + X.V := by
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab]
      exact (min_le_left _ _).trans (by linarith only [hU₀, hV₀])
    · rw [min_eq_right hab]
      exact (min_le_right _ _).trans (by linarith only [hD₀, hE₀])
  have hRbase : R ≤ p * (T + R) := by
    have hh := mul_nonneg (sub_nonneg.mpr hp) hR
    have ht := mul_nonneg hp₀ hT
    nlinarith only [hh, ht]
  have hTbase : T ≤ p * (T + R) := by
    have hh := mul_nonneg (sub_nonneg.mpr hp) hT
    have ht := mul_nonneg hp₀ hR
    nlinarith only [hh, ht]
  have hpRbase : p * R ≤ p * (T + R) := mul_le_mul_of_nonneg_left (by linarith only [hT]) hp₀
  have hcost : min (a + X.D + X.E) (b + X.U + X.V) ≤ B * (p * (T + R)) := by
    have hr' := mul_le_mul_of_nonneg_left hRbase (show 0 ≤ 2 * Real.sqrt C by positivity)
    have ht' := mul_le_mul_of_nonneg_left hTbase (by norm_num : (0 : ℝ) ≤ 2)
    dsimp only [B]
    linarith only [hmin, hroot, haxes, hpRbase, hr', ht']
  have hB : B ≤ p := by simpa only [Real.rpow_zero, mul_one] using hk N (by omega)
  calc
    _ ≤ B * (p * (T + R)) := hcost
    _ ≤ p * (p * (T + R)) := mul_le_mul_of_nonneg_right hB (mul_nonneg hp₀ (add_nonneg hT hR))
    _ = _ := by
      dsimp only [p, R]
      rw [← mul_assoc, ← Real.rpow_add hn, add_halves]
      ring

end PaperP1.DeterminantSevenTwelfthsCosts
