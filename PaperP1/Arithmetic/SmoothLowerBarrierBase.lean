module

public import PaperP1.Analysis.PolynomialSmoothDensity
public import PaperP1.Analysis.SmoothLowerBarrierProfile

/-! # An internal base range for the fine smooth-count lower barrier

The fixed polynomial smooth-density theorem supplies one positive
constant for every integer cutoff and every bounded relative height.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothLowerBarrierBase

open OrdinarySmoothCensus SmoothRecursiveLower SmoothLowerBarrierProfile

theorem uniform_base (ε T : ℝ) (hε : 0 ≤ ε) (hT : Real.exp 1 ≤ T) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ∃ Y₀ : ℕ, 2 ≤ Y₀ ∧
      ∀ Y ≥ Y₀, ∀ X : ℕ, 1 ≤ X → Real.log X / Real.log Y ≤ T + 1 →
        a * X * density ε T (Real.log X / Real.log Y) ≤ (smoothUpTo X Y).card := by
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  let α := 1 / (T + 2)
  have hα : 0 < α := by dsimp only [α]; positivity
  obtain ⟨δ, hδ, X₀, hpoly⟩ := PolynomialSmoothDensity.uniform_lower α hα
  let a := min δ 1
  have ha : 0 < a := lt_min hδ (by norm_num)
  have haδ : a ≤ δ := min_le_left _ _
  have ha1 : a ≤ 1 := min_le_right _ _
  refine ⟨a, ha, ha1, max X₀ 2, by omega, ?_⟩
  intro Y hY X hX hratio
  have hy : (1 : ℝ) < Y := by exact_mod_cast (show 1 < Y by omega)
  have hlogY : 0 < Real.log Y := Real.log_pos hy
  have hx : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hcount : a * (X : ℝ) ≤ (smoothUpTo X Y).card := by
    by_cases hlarge : max X₀ 2 ≤ X
    · have hheight := (div_le_iff₀ hlogY).mp hratio
      have hexp : Real.log X * α ≤ Real.log Y := by
        have hid : Real.log X * α = Real.log X / (T + 2) := by dsimp only [α]; ring
        rw [hid]
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < T + 2)).mpr
        nlinarith only [hheight, hlogY]
      have hpower : (X : ℝ) ^ α ≤ Y := by
        rw [Real.rpow_def_of_pos hx]
        exact (Real.exp_le_exp.mpr hexp).trans_eq (Real.exp_log (by linarith only [hy] : (0 : ℝ) < Y))
      have hcut : ⌊(X : ℝ) ^ α⌋₊ ≤ Y := by
        have hh := (Nat.floor_le (Real.rpow_nonneg hx.le α)).trans hpower
        exact_mod_cast hh
      have hc : ((smoothUpTo X ⌊(X : ℝ) ^ α⌋₊).card : ℝ) ≤ (smoothUpTo X Y).card := by
        exact_mod_cast Finset.card_le_card (smoothUpTo_mono (le_refl X) hcut)
      exact (mul_le_mul_of_nonneg_right haδ hx.le).trans ((hpoly X hlarge).trans hc)
    · have hxy : X ≤ Y := by omega
      rw [smooth_below_card hxy]
      exact mul_le_of_le_one_left (Nat.cast_nonneg X) ha1
  exact (mul_le_of_le_one_right (by positivity : (0 : ℝ) ≤ a * X)
    (density_le_one ε T _ hε hT)).trans hcount

end PaperP1.SmoothLowerBarrierBase
