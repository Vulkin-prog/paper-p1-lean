module

public import PaperP1.Analysis.DeterminantLogScale
public import PaperP1.Asymptotics.HalfCountSchedule
public import PaperP1.Asymptotics.SplitQuadraticCongruenceCount
public import Mathlib.Algebra.Order.Floor.Semiring

/-! # The actual rounded determinant scale is uniformly admissible -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantHorizontalScale

open Filter PaperP1.DeterminantLogScale

def horizontalScale (N : ℕ) (D E U V ζ : ℝ) : ℕ :=
  ⌈(N : ℝ) ^ ζ * Real.exp (logShape N D E U V)⌉₊

theorem horizontalScale_pos {N : ℕ} (hN : 0 < N) (D E U V ζ : ℝ) :
    0 < horizontalScale N D E U V ζ := by
  apply Nat.ceil_pos.mpr
  exact mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast hN) _) (Real.exp_pos _)

theorem horizontalScale_lower (N : ℕ) (D E U V ζ : ℝ) :
    (N : ℝ) ^ ζ * Real.exp (logShape N D E U V) ≤ horizontalScale N D E U V ζ := Nat.le_ceil _

theorem shape_exponent_eventually (C η : ℝ) (hC : 0 < C) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ c₁ c₂ D E U V : ℝ,
      0 < c₁ → 0 < c₂ → 0 < D → 0 < E → 0 < U → 0 < V →
      1 ≤ c₁ * c₂ → 1 ≤ D * E → c₁ * D ^ 2 * U ≤ C * N → c₂ * E ^ 2 * V ≤ C * N →
        logShape N D E U V ≤ (9 / 16 + η) * Real.log N := by
  have hf : Tendsto (fun H : ℝ ↦ Real.log C / H) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have ht : Tendsto (fun H : ℝ ↦ (9 / 16 : ℝ) * (1 + Real.log C / H) ^ 2) atTop (nhds (9 / 16)) := by
    have hh := (((tendsto_const_nhds (x := (1 : ℝ))).add hf).pow 2).const_mul (9 / 16)
    simpa only [add_zero, one_pow, mul_one] using hh
  have hnlog : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, h⟩ := eventually_atTop.mp
    ((ht.comp hnlog).eventually (eventually_lt_nhds (by linarith only [hη] : (9 / 16 : ℝ) < 9 / 16 + η)))
  refine ⟨N₀, ?_⟩
  intro N hN c₁ c₂ D E U V hc₁ hc₂ hD hE hU hV hcoeff hDE hfirst hsecond
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have he := h N (by omega)
  change (9 / 16 : ℝ) * (1 + Real.log C / Real.log N) ^ 2 < 9 / 16 + η at he
  have hb := shape_bound hn hC hc₁ hc₂ hD hE hU hV hcoeff hDE hfirst hsecond
  have hm := mul_le_mul_of_nonneg_right he.le (Real.log_pos hn).le
  exact hb.trans (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hm)

theorem upper_of_shape {N : ℕ} (hN : 2 ≤ N) (D E U V ζ η : ℝ) (hζ : 0 ≤ ζ) (hη : 0 ≤ η)
    (hshape : logShape N D E U V ≤ (9 / 16 + η) * Real.log N) :
    (horizontalScale N D E U V ζ : ℝ) ≤ 2 * (N : ℝ) ^ (ζ + 9 / 16 + η) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hprod : (N : ℝ) ^ ζ * Real.exp (logShape N D E U V) ≤ (N : ℝ) ^ (ζ + 9 / 16 + η) := by
    calc
      _ ≤ (N : ℝ) ^ ζ * Real.exp ((9 / 16 + η) * Real.log N) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hshape) (Real.rpow_nonneg hn.le _)
      _ = _ := by
        simp only [Real.rpow_def_of_pos hn]
        rw [← Real.exp_add]
        congr 1
        ring
  have hpow : 1 ≤ (N : ℝ) ^ (ζ + 9 / 16 + η) :=
    Real.one_le_rpow hn1 (by linarith only [hζ, hη])
  have hc := (Nat.ceil_lt_add_one
    (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ ζ * Real.exp (logShape N D E U V))).le
  change (horizontalScale N D E U V ζ : ℝ) ≤ (N : ℝ) ^ ζ * Real.exp (logShape N D E U V) + 1 at hc
  linarith only [hc, hprod, hpow]

theorem uniform_upper (C ζ η : ℝ) (hC : 0 < C) (hζ : 0 ≤ ζ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ c₁ c₂ D E U V : ℝ,
      0 < c₁ → 0 < c₂ → 0 < D → 0 < E → 0 < U → 0 < V →
      1 ≤ c₁ * c₂ → 1 ≤ D * E → c₁ * D ^ 2 * U ≤ C * N → c₂ * E ^ 2 * V ≤ C * N →
        (horizontalScale N D E U V ζ : ℝ) ≤ (N : ℝ) ^ (ζ + 9 / 16 + η) := by
  obtain ⟨NS, hS⟩ := shape_exponent_eventually C (η / 2) hC (by positivity)
  obtain ⟨NF, hF⟩ := HalfCountSchedule.factor_absorption 2 (ζ + 9 / 16 + η / 2) (η / 2) (by positivity)
  refine ⟨max NS NF, ?_⟩
  intro N hN c₁ c₂ D E U V hc₁ hc₂ hD hE hU hV hcoeff hDE hfirst hsecond
  have hs := hS N (by omega) c₁ c₂ D E U V hc₁ hc₂ hD hE hU hV hcoeff hDE hfirst hsecond
  have hm := upper_of_shape (by omega : 2 ≤ N) D E U V ζ (η / 2) hζ (by positivity) hs
  have hf := hF N (by omega)
  simpa only [show ζ + (9 : ℝ) / 16 + η / 2 + η / 2 = ζ + 9 / 16 + η by ring] using hm.trans hf

theorem uniform_admissible (C ζ K A : ℝ) (hC : 0 < C) (hζ : 0 ≤ ζ) (hζsmall : ζ < 7 / 16) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ h : ℕ, 0 < h → (h : ℝ) ≤ K * (Real.log N) ^ A →
      ∀ c₁ c₂ D E U V : ℝ, 0 < c₁ → 0 < c₂ → 0 < D → 0 < E → 0 < U → 0 < V →
        1 ≤ c₁ * c₂ → 1 ≤ D * E → c₁ * D ^ 2 * U ≤ C * N → c₂ * E ^ 2 * V ≤ C * N →
          0 < horizontalScale N D E U V ζ ∧
            (horizontalScale N D E U V ζ : ℝ) * h ≤ N ∧
              (horizontalScale N D E U V ζ : ℝ) ≤ (N : ℝ) / h := by
  let δ := (1 - (ζ + 9 / 16)) / 3
  have hδ : 0 < δ := by dsimp [δ]; linarith only [hζsmall]
  obtain ⟨NM, hM⟩ := uniform_upper C ζ δ hC hζ hδ
  obtain ⟨NH, hH⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow K A δ hδ
  refine ⟨max NM NH, ?_⟩
  intro N hN h hh hshift c₁ c₂ D E U V hc₁ hc₂ hD hE hU hV hcoeff hDE hfirst hsecond
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hm := hM N (by omega) c₁ c₂ D E U V hc₁ hc₂ hD hE hU hV hcoeff hDE hfirst hsecond
  have hhp := hshift.trans (hH N (by omega))
  have hprod : (horizontalScale N D E U V ζ : ℝ) * h ≤ N := by
    calc
      _ ≤ (N : ℝ) ^ (ζ + 9 / 16 + δ) * (N : ℝ) ^ δ :=
        mul_le_mul hm hhp (Nat.cast_nonneg _) (Real.rpow_nonneg hn.le _)
      _ = (N : ℝ) ^ (ζ + 9 / 16 + δ + δ) := (Real.rpow_add hn _ _).symm
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [δ]; linarith only [hζsmall])
      _ = _ := Real.rpow_one _
  exact ⟨horizontalScale_pos (by omega) D E U V ζ, hprod,
    (le_div_iff₀ (by exact_mod_cast hh : (0 : ℝ) < h)).mpr hprod⟩

theorem relative_vertical_bound {c₁ c₂ d e u h s₀ N ρ M : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hd : 0 < d) (he : 0 < e) (hu : 0 < u) (hs₀ : 0 < s₀)
    (hN : 0 < N) (hρ : 0 < ρ) (hM : 1 ≤ M)
    (hsource : ρ * N ≤ DeterminantRelativeChart.source c₁ d u)
    (ha : |DeterminantRelativeChart.alpha d e s₀| ≤ 1 / M) (hMh : M * |h| ≤ N) :
    |DeterminantRelativeChart.error c₁ c₂ e u h s₀| ≤ 4 / (ρ * M) := by
  have hβ := DeterminantRelativeChart.error_bound_at_scale (h := h) hc₁ hc₂ hd he hu hs₀ hN hρ hsource
    (DeterminantRelativeChart.alpha_le_one hM ha)
  apply hβ.trans
  apply (div_le_div_iff₀ (mul_pos hρ hN) (mul_pos hρ (by linarith : 0 < M))).mpr
  have hh := mul_le_mul_of_nonneg_left hMh (by positivity : (0 : ℝ) ≤ 4 * ρ)
  nlinarith only [hh]

end PaperP1.DeterminantHorizontalScale
