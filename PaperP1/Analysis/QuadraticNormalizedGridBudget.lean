module

public import PaperP1.Analysis.QuadraticNormalizedGridCount

/-! # A single quadratic-degree polynomial-logarithmic profile for the actual global count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticNormalizedGridBudget

open MvPolynomial QuadraticNormalizedGridCount JointExceptionalComponentGridCount

theorem budget (D k N : ℕ) (hD : 1 ≤ D) :
    ((D ^ 2 * (123 * (k + 1) ^ 6) : ℕ) : ℝ) +
      2 * (((D ^ 2 * (123 * (k + 1) ^ 6) + D * (2 * D + 4)) : ℕ) : ℝ) * componentScale k N ≤
      300000 * Real.exp 4 * (D : ℝ) ^ 2 * ((Nat.log2 (2 * N) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 16 := by
  let d : ℝ := D
  let K : ℝ := ((k + 1 : ℕ) : ℝ)
  let L : ℝ := ((Nat.log2 (2 * N) + 1 : ℕ) : ℝ)
  let e : ℝ := Real.exp 4
  have hd : 1 ≤ d := by dsimp [d]; exact_mod_cast hD
  have hK : 1 ≤ K := by dsimp [K]; exact_mod_cast (show 1 ≤ k + 1 by omega)
  have hL : 1 ≤ L := by dsimp [L]; exact_mod_cast (show 1 ≤ Nat.log2 (2 * N) + 1 by omega)
  have he : 1 ≤ e := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 4)
  have hK6 : 1 ≤ K ^ 6 := one_le_pow₀ hK
  have hK10 : 1 ≤ K ^ 10 := one_le_pow₀ hK
  have hK616 : K ^ 6 ≤ K ^ 16 := pow_le_pow_right₀ hK (by decide)
  have hd2 : d ≤ d ^ 2 := by nlinarith only [hd, sq_nonneg (d - 1)]
  have hsink : d * (2 * d + 4) ≤ 6 * d ^ 2 := by nlinarith only [hd2]
  have h6scale : 6 * d ^ 2 ≤ 6 * d ^ 2 * K ^ 6 :=
    le_mul_of_one_le_right (by positivity) hK6
  have hfamily : 123 * d ^ 2 * K ^ 6 + d * (2 * d + 4) ≤ 129 * d ^ 2 * K ^ 6 := by
    nlinarith only [hsink, h6scale]
  have heL : 1 ≤ e * L := one_le_mul_of_one_le_of_one_le he hL
  have heLK : 1 ≤ e * L * K ^ 10 := one_le_mul_of_one_le_of_one_le heL hK10
  have hA : componentScale k N ≤ 1026 * e * L * K ^ 10 := by
    change 2 + 1024 * e * L * K ^ 10 ≤ _
    nlinarith only [heLK]
  have hB : 123 * d ^ 2 * K ^ 6 ≤ 123 * e * d ^ 2 * L * K ^ 16 := by
    calc
      _ ≤ 123 * d ^ 2 * K ^ 16 := mul_le_mul_of_nonneg_left hK616 (by positivity)
      _ ≤ (e * L) * (123 * d ^ 2 * K ^ 16) := le_mul_of_one_le_left (by positivity) heL
      _ = _ := by ring
  have hmain : 2 * (123 * d ^ 2 * K ^ 6 + d * (2 * d + 4)) * componentScale k N ≤
      264708 * e * d ^ 2 * L * K ^ 16 := by
    calc
      _ ≤ 2 * (129 * d ^ 2 * K ^ 6) * (1026 * e * L * K ^ 10) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hfamily (by norm_num)) hA
          (componentScale_nonneg k N) (by positivity)
      _ = _ := by ring
  have hBcast : ((D ^ 2 * (123 * (k + 1) ^ 6) : ℕ) : ℝ) = 123 * d ^ 2 * K ^ 6 := by
    dsimp [d, K]
    push_cast
    ring
  have hScast : ((D * (2 * D + 4) : ℕ) : ℝ) = d * (2 * d + 4) := by
    dsimp [d]
    push_cast
    rfl
  rw [Nat.cast_add, hBcast, hScast]
  change 123 * d ^ 2 * K ^ 6 + 2 * (123 * d ^ 2 * K ^ 6 + d * (2 * d + 4)) * componentScale k N ≤
    300000 * e * d ^ 2 * L * K ^ 16
  have hnonneg : 0 ≤ e * d ^ 2 * L * K ^ 16 := by positivity
  nlinarith only [hB, hmain, hnonneg]

theorem point_count (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (k : ℕ) (hk : 1 ≤ k) (hkD : k < P.totalDegree)
    (N : ℕ) (hN : 0 < N) (hlog : Real.log (N : ℝ) ≤ k)
    (S : Finset (Fin 2 → ℝ)) (hcurve : ∀ z ∈ S, eval z P = 0)
    (hbox : ∀ z ∈ S, z ∈ unitBox)
    (hgrid : ∀ w ∈ S, ∃ z : Fin 2 → ℤ, ∀ i, w i = (z i : ℝ) / N) :
    (S.card : ℝ) ≤ 300000 * Real.exp 4 * (P.totalDegree : ℝ) ^ 2 *
      ((Nat.log2 (2 * N) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 16 :=
  (QuadraticNormalizedGridCount.point_count P hP k hk hkD N hN hlog S hcurve hbox hgrid).trans
    (budget P.totalDegree k N (by omega))

end PaperP1.QuadraticNormalizedGridBudget
