module

public import PaperP1.Analysis.VerticalGridLattice
public import PaperP1.Arithmetic.DeterminantSignedBoxes

/-! # Every actual signed source solution lies in the second lattice box -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualVerticalLattice

open Finset PaperP1.DeterminantSourceBox PaperP1.DeterminantSignedBoxes
open PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantRelativeIntervals
open PaperP1.EffectiveSourceCoordinates PaperP1.BinaryLatticeMinimum

def transform {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ) (M k : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let U := scale N X.c₁ X.D
  let V := scale N X.c₂ X.E
  PaperP1.RelativeIntervalLattice.transform (2 * C * V) (C * U) (2 * M)
    (intervalCenter (2 * M) (2 * C * V) (C * U) (PaperP1.QuadraticIntervalGrid.grid M k))

theorem grid_center_identity {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ)
    (hN : 0 < N) (hC : 0 < C) (M k : ℕ) (hM : 0 < M) :
    intervalCenter (2 * M) (2 * C * scale N X.c₂ X.E) (C * scale N X.c₁ X.D)
      (PaperP1.QuadraticIntervalGrid.grid M k) = PaperP1.ActualVerticalGrid.gridCenter M k X.c₁ X.c₂ X.D X.E := by
  have hc₁ : 0 < X.c₁ := by linarith [X.c₁_ge_one]
  have hc₂ : 0 < X.c₂ := by linarith [X.c₂_ge_one]
  have hD : 0 < X.D := by linarith [X.D_ge_one]
  have hE : 0 < X.E := by linarith [X.E_ge_one]
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hU : 0 < scale N X.c₁ X.D := by unfold scale; positivity
  rw [VerticalGridLattice.center_identity M _ hM hC.ne' hU.ne',
    ratio_identity hn.ne' hc₁.ne' hc₂.ne' hD.ne' hE.ne']
  rfl

theorem actual_point_box {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ)
    (hN : 0 < N) (hC : 0 < C) (hρ : 0 < ρ) (M : ℕ) (hM : 4 ≤ M)
    (h : ℤ) (hMh : (M : ℝ) * |(h : ℝ)| ≤ N)
    (S : Finset Quad) (hS : SignedPopulation X h S) (p : Quad) (hp : p ∈ S) :
    ∀ i, |realImage (transform X M (intervalIndex M X.D X.E p.1.1 p.1.2))
      ![(p.2.2 : ℤ), (p.2.1 : ℤ)] i| ≤ 2 * (49 + 16 / ρ) := by
  have hc₁ : 0 < X.c₁ := by linarith [X.c₁_ge_one]
  have hc₂ : 0 < X.c₂ := by linarith [X.c₂_ge_one]
  have hD : 0 < X.D := by linarith [X.D_ge_one]
  have hE : 0 < X.E := by linarith [X.E_ge_one]
  have hU : 0 < X.U := by linarith [X.U_ge_one]
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hd := hS.d_bounds p hp
  have he := hS.e_bounds p hp
  have hu := hS.u_bounds p hp
  have huR : 0 < (p.2.1 : ℝ) := hU.trans_le hu.1
  have huN : 0 < p.2.1 := by exact_mod_cast huR
  have hsource : ρ * N ≤ PaperP1.DeterminantRelativeChart.source X.c₁ p.1.1 p.2.1 := by
    have hsquare := pow_le_pow_left₀ hD.le hd.1 2
    have hprod := mul_le_mul hsquare hu.1 hU.le (sq_nonneg (p.1.1 : ℝ))
    have hscaled := mul_le_mul_of_nonneg_left hprod hc₁.le
    unfold PaperP1.DeterminantRelativeChart.source
    nlinarith only [X.first_lower, hscaled]
  have hUb := scale_bounds hn X.c₁_ge_one X.D_ge_one X.U_ge_one X.first_lower X.first_upper
  have hVb := scale_bounds hn X.c₂_ge_one X.E_ge_one X.V_ge_one X.second_lower X.second_upper
  have hratio := ratio_identity hn.ne' hc₁.ne' hc₂.ne' hD.ne' hE.ne'
  have herr := ActualVerticalGrid.actual_grid_error M hM hD hE hc₁ hc₂ hn hρ hMh p
    hd.1 hd.2 he.1 he.2 huN hsource (hS.equation p hp)
  have huhi : (p.2.1 : ℝ) ≤ 2 * C * scale N X.c₁ X.D := by linarith [hUb.2.2.1]
  have hK : (1 : ℝ) ≤ 49 + 16 / ρ := by
    have ht : (0 : ℝ) ≤ 16 / ρ := by positivity
    linarith
  apply VerticalGridLattice.point_box M _ (by omega) hC hUb.1 hVb.1 hK
    ![(p.2.2 : ℤ), (p.2.1 : ℤ)]
  · simpa using huR
  · simpa using huhi
  · simpa [ActualRelativeDeterminant.secondRatio, ActualVerticalGrid.gridCenter, hratio] using herr

end PaperP1.ActualVerticalLattice
