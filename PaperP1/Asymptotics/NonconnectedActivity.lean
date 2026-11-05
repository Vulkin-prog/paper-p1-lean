module

public import PaperP1.Model.BoundedComponentActivity
public import PaperP1.Asymptotics.FixedAbsoluteActivity

/-! # Every bounded range of nonconnected actual absolute centered activity has exponent4/3 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonconnectedActivity

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies

theorem uniform_bound (R : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ G ∧ I.Nonempty ∧ I.card ≤ R ∧ ¬ Connected L I) →
        (∑ I ∈ F, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-4 / 3 + ε) := by
  classical
  let δ := min (ε / 4) (1 / 12)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδε : δ ≤ ε / 4 := min_le_left _ _
  have hδsmall : δ ≤ 1 / 12 := min_le_right _ _
  let B : ℝ := R + 1
  let D : ℝ := B ^ 2 / 2 * Real.exp 1
  obtain ⟨NA, _hNA, ha⟩ := FixedAbsoluteActivity.uniform_range R C δ hδ
  obtain ⟨NZ, hz⟩ := HalfCountSchedule.factor_absorption B (-7 / 12) (7 / 12) (by norm_num)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption D (-4 / 3 + ε / 2) (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨10 + NA + NZ + NF + NG, by omega, ?_⟩
  intro N hN L hband G hG F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  let W := ∑ I ∈ BoundedComponentActivity.population G R, |infiniteCenteredCoefficient L I|
  let T := (N : ℝ) ^ (-2 / 3 + δ)
  have hW : 0 ≤ W := sum_nonneg fun I _ ↦ abs_nonneg _
  have hT : 0 ≤ T := Real.rpow_nonneg hn.le _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hWbound : W ≤ B * T := by
    convert BoundedComponentActivity.sum_bound G L R T hT
      (fun r hr hcap ↦ ha N (by omega) L hband r (by omega) hcap G hG) using 1; simp only [B, Nat.cast_add, Nat.cast_one]
  have hWone : W ≤ 1 := by
    calc
      _ ≤ B * T := hWbound
      _ ≤ B * (N : ℝ) ^ (-7 / 12 : ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδsmall])) hB
      _ ≤ (N : ℝ) ^ ((-7 / 12 : ℝ) + 7 / 12) := hz N (by omega)
      _ = 1 := by norm_num
  have hquad : W ^ 2 / 2 * Real.exp W ≤ (B * T) ^ 2 / 2 * Real.exp 1 :=
    mul_le_mul (div_le_div_of_nonneg_right (pow_le_pow_left₀ hW hWbound 2) (by norm_num))
      (Real.exp_le_exp.mpr hWone) (Real.exp_nonneg W) (by positivity)
  have hTsquare : T ^ 2 = (N : ℝ) ^ (-4 / 3 + 2 * δ) := by
    dsimp only [T]
    rw [pow_two, ← Real.rpow_add hn]
    congr 1
    ring
  calc
    _ ≤ W ^ 2 / 2 * Real.exp W := BoundedComponentActivity.finite_bound G L R hL F hF
    _ ≤ (B * T) ^ 2 / 2 * Real.exp 1 := hquad
    _ = D * (N : ℝ) ^ (-4 / 3 + 2 * δ) := by rw [mul_pow, hTsquare]; dsimp only [D]; ring
    _ ≤ D * (N : ℝ) ^ (-4 / 3 + ε / 2) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδε])) (by dsimp [D]; positivity)
    _ ≤ (N : ℝ) ^ ((-4 / 3 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.NonconnectedActivity
