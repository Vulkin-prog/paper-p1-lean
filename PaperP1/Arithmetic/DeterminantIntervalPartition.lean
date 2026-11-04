module

public import PaperP1.Analysis.DeterminantRelativeIntervals

/-! # Exact actual-point partition into finitely many small relative charts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantIntervalPartition

open Finset PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantRelativeIntervals
  PaperP1.DeterminantRelativeChart PaperP1.ActualRelativeDeterminant

def cluster (M : ℕ) (D E : ℝ) (k : ℕ) (S : Finset Quad) : Finset Quad :=
  S.filter (fun p ↦ intervalIndex M D E p.1.1 p.1.2 = k)

theorem mem_cluster (M : ℕ) (D E : ℝ) (k : ℕ) (S : Finset Quad) (p : Quad) :
    p ∈ cluster M D E k S ↔ p ∈ S ∧ intervalIndex M D E p.1.1 p.1.2 = k := by
  exact mem_filter

theorem finite_partition (M : ℕ) (hM : 4 ≤ M) {D E : ℝ} (hD : 0 < D) (hE : 0 < E)
    (S : Finset Quad)
    (hbox : ∀ p ∈ S, D ≤ p.1.1 ∧ (p.1.1 : ℝ) ≤ 2 * D ∧ E ≤ p.1.2 ∧ (p.1.2 : ℝ) ≤ 2 * E) :
    S.card = ∑ k ∈ intervalIndices M, (cluster M D E k S).card := by
  apply card_eq_sum_card_fiberwise
  intro p hp
  have h := hbox p hp
  exact index_mem M hM hD hE h.1 h.2.1 h.2.2.1 h.2.2.2

theorem center_positive (M : ℕ) (hM : 0 < M) {D E : ℝ} (hD : 0 < D) (hE : 0 < E)
    {k : ℕ} (hk : k ∈ intervalIndices M) : 0 < intervalCenter M D E k := by
  have hkN : 0 < k := (mem_Icc.mp hk).1
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkN
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  exact div_pos (mul_pos (div_pos hD hE) hkR) hMR

theorem point_center_bounds (M : ℕ) (hM : 4 ≤ M) {D E : ℝ} (hD : 0 < D) (hE : 0 < E)
    (S : Finset Quad) (p : Quad) (k : ℕ) (hp : p ∈ cluster M D E k S)
    (hdlo : D ≤ p.1.1) (hdhi : (p.1.1 : ℝ) ≤ 2 * D)
    (helo : E ≤ p.1.2) (hehi : (p.1.2 : ℝ) ≤ 2 * E) :
    D / (4 * E) ≤ intervalCenter M D E k ∧ intervalCenter M D E k ≤ 2 * D / E := by
  rw [← (mem_cluster M D E k S p).mp hp |>.2]
  exact DeterminantRelativeIntervals.center_bounds M hM hD hE hdlo hdhi helo hehi

theorem point_alpha_bound (M : ℕ) (hM : 4 ≤ M) {D E : ℝ} (hD : 0 < D) (hE : 0 < E)
    (S : Finset Quad) (p : Quad) (k : ℕ) (hp : p ∈ cluster M D E k S)
    (hdlo : D ≤ p.1.1) (hdhi : (p.1.1 : ℝ) ≤ 2 * D)
    (helo : E ≤ p.1.2) (hehi : (p.1.2 : ℝ) ≤ 2 * E) :
    |relativeAlpha (intervalCenter M D E k) p| ≤ 4 / M := by
  rw [← (mem_cluster M D E k S p).mp hp |>.2]
  exact alpha_absolute_bound M hM hD hE hdlo hdhi helo hehi

theorem point_vertical_bound (M : ℕ) (hM : 4 ≤ M) {D E : ℝ} (hD : 0 < D) (hE : 0 < E)
    (S : Finset Quad) (p : Quad) (k : ℕ) (hp : p ∈ cluster M D E k S)
    (hdlo : D ≤ p.1.1) (hdhi : (p.1.1 : ℝ) ≤ 2 * D)
    (helo : E ≤ p.1.2) (hehi : (p.1.2 : ℝ) ≤ 2 * E)
    {c₁ c₂ h N ρ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hu : 0 < p.2.1)
    (hN : 0 < N) (hρ : 0 < ρ) (hsource : ρ * N ≤ source c₁ p.1.1 p.2.1) :
    |relativeError c₁ c₂ h (intervalCenter M D E k) p| ≤ 4 * |h| / (ρ * N) := by
  have hcenter := point_center_bounds M hM hD hE S p k hp hdlo hdhi helo hehi
  have hs₀ : 0 < intervalCenter M D E k := (div_pos hD (by positivity : 0 < 4 * E)).trans_le hcenter.1
  have hMR : (4 : ℝ) ≤ M := by exact_mod_cast hM
  have ha := point_alpha_bound M hM hD hE S p k hp hdlo hdhi helo hehi
  have ha₁ : |relativeAlpha (intervalCenter M D E k) p| ≤ 1 := by
    exact ha.trans ((div_le_one (by linarith only [hMR] : (0 : ℝ) < M)).mpr hMR)
  exact error_bound_at_scale hc₁ hc₂ (hD.trans_le hdlo) (hE.trans_le helo)
    (by exact_mod_cast hu) hs₀ hN hρ hsource ha₁

end PaperP1.DeterminantIntervalPartition
