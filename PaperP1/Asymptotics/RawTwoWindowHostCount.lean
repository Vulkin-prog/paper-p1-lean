module

public import PaperP1.Model.RawTwoWindowHosts
public import PaperP1.Asymptotics.ExpSqrtLog
public import PaperP1.Asymptotics.UniformSubpolynomialPower

/-! # Unrestricted raw host count for every moving logarithmic width

The width is only bounded above by a fixed multiple of `log N`. In
particular, no fixed offset from a critical length and no evenness of the
selected vertices is required. Local relations and diagonal hosts remain
in the counted set.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RawTwoWindowHostCount

open PaperP1.RawTwoWindowHosts

def envelope (B : ℕ) : ℝ :=
  (8 * Real.sqrt 3) * ((B + 1 : ℝ) * Real.exp (growthConstant * Real.sqrt B))

theorem envelope_nonneg (B : ℕ) : 0 ≤ envelope B := by
  unfold envelope
  positivity

theorem uniform_envelope (D : ℝ) (hD : 0 ≤ D) :
    PaperP1.UniformSubpolynomialOn (fun N B ↦ (B : ℝ) ≤ D * Real.log N)
      (fun _ B ↦ envelope B) := by
  have hpoly := PaperP1.ExpSqrtLog.uniformSubpolynomialOn_linear_log_add_one
    (fun N B ↦ (B : ℝ) ≤ D * Real.log N) (fun _ B ↦ B) D hD (fun _ _ h ↦ h)
  have hexp := PaperP1.ExpSqrtLog.uniformSubpolynomialOn_exp_sqrt_of_le_log
    (fun N B ↦ (B : ℝ) ≤ D * Real.log N) (fun _ B ↦ B)
    growthConstant D growthConstant_nonneg hD (fun _ _ h ↦ h)
  exact PaperP1.ExpSqrtLog.uniformSubpolynomialOn_const_mul (8 * Real.sqrt 3)
    (PaperP1.ExpSqrtLog.uniformSubpolynomialOn_mul hpoly hexp)

theorem rpow_three_halves {x : ℝ} (hx : 0 < x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx,
    Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem finite_envelope_bound {N B : ℕ} (hN : 2 ≤ N) (hB : 1 ≤ B) (hBN : B ≤ N) :
    ((hosts N B).card : ℝ) ≤ envelope B * (N : ℝ) ^ (3 / 2 : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  refine (finite_bound hN hB hBN).trans ?_
  calc
    8 * B * N * Real.sqrt (3 * N) * Real.exp (growthConstant * Real.sqrt B) ≤
        8 * (B + 1 : ℝ) * N * Real.sqrt (3 * N) *
          Real.exp (growthConstant * Real.sqrt B) := by gcongr; linarith
    _ = envelope B * (N : ℝ) ^ (3 / 2 : ℝ) := by
      rw [rpow_three_halves hn, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
      unfold envelope
      ring

theorem uniform_bound (D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ B : ℕ, 1 ≤ B →
      (B : ℝ) ≤ D * Real.log N →
      ((hosts N B).card : ℝ) ≤ (N : ℝ) ^ (3 / 2 + ε : ℝ) := by
  obtain ⟨NF, hF⟩ := PaperP1.UniformSubpolynomialPower.bound (uniform_envelope D hD) ε hε
  obtain ⟨NB, hNB⟩ := PaperP1.ExpSqrtLog.linear_log_add_one_pow_le_nat_eventually D hD 1 (by omega)
  refine ⟨max (max NF NB) 2, ?_⟩
  intro N hN B hB hlog
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hBN : B ≤ N := by
    have hw := hNB N (by omega) B hlog
    simp only [pow_one] at hw
    have : (B : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hf := hF N (by omega) B hlog
  rw [abs_of_nonneg (envelope_nonneg B)] at hf
  calc
    ((hosts N B).card : ℝ) ≤ envelope B * (N : ℝ) ^ (3 / 2 : ℝ) :=
      finite_envelope_bound (by omega) hB hBN
    _ ≤ (N : ℝ) ^ ε * (N : ℝ) ^ (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right hf (Real.rpow_nonneg hn.le _)
    _ = (N : ℝ) ^ (3 / 2 + ε : ℝ) := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.RawTwoWindowHostCount
