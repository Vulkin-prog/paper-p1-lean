module

public import PaperP1.Analysis.MonomialCountingParameters

/-! # Explicit polynomial-degree and logarithmic per-map grid counts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SimplifiedUnitMapGridCount

open MvPolynomial Set TotalDegreeMonomials TotalDegreeMonomialFamily AffineUnitGraphParametrization
open scoped ContDiff

theorem point_count (k : ℕ) (hk : 1 ≤ k) (N : ℕ) (hN : 0 < N)
    (ψ : Fin 2 → ℝ → ℝ) (hψ : ∀ i, ContDiffOn ℝ ∞ (ψ i) (Ioo (0 : ℝ) 1))
    (hjet : UnitJets (Fintype.card (Index k) - 1) ψ)
    (hpoly : ∀ Q : MvPolynomial (Fin 2) ℝ, Q ≠ 0 → Q.totalDegree ≤ k →
      ∀ S : Finset (Fin 2 → ℝ),
        (∀ w ∈ S, (∃ t ∈ Ioo (0 : ℝ) 1, (fun i ↦ ψ i t) = w) ∧ eval w Q = 0) →
          S.card < Fintype.card (Index k))
    (S : Finset (Fin 2 → ℝ))
    (hS : ∀ w ∈ S, ∃ t ∈ Ioo (0 : ℝ) 1, (fun i ↦ ψ i t) = w)
    (hgrid : ∀ w ∈ S, ∃ z : Fin 2 → ℤ, ∀ i, w i = (z i : ℝ) / N) :
    (S.card : ℝ) ≤ 32 * ((k + 1 : ℕ) : ℝ) ^ 8 * (N : ℝ) ^ (4 / ((k : ℝ) + 3)) := by
  have hh := UnitMapGridPointCount.point_count k hk N hN ψ hψ hjet hpoly S hS hgrid
  dsimp only at hh
  rw [MonomialCountingParameters.height_exponent k hk] at hh
  have hcard : (Fintype.card (Index k) : ℝ) ≤ (((k + 1 : ℕ) : ℝ)) ^ 2 := by
    exact_mod_cast index_card_le k
  have hcube := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 3
  have hcoef : 32 * (Fintype.card (Index k) : ℝ) ^ 3 * ((k + 1 : ℕ) : ℝ) ^ 2 ≤
      32 * ((k + 1 : ℕ) : ℝ) ^ 8 := by
    calc
      _ ≤ 32 * ((((k + 1 : ℕ) : ℝ)) ^ 2) ^ 3 * ((k + 1 : ℕ) : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcube (by norm_num)) (by positivity)
      _ = _ := by ring
  exact hh.trans (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (Nat.cast_nonneg _) _))

theorem logarithmic_power_bound (k N : ℕ) (hN : 0 < N) (hlog : Real.log (N : ℝ) ≤ k) :
    (N : ℝ) ^ (4 / ((k : ℝ) + 3)) ≤ Real.exp 4 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.rpow_def_of_pos hNR]
  apply Real.exp_le_exp.mpr
  have he : Real.log (N : ℝ) * (4 / ((k : ℝ) + 3)) =
      (4 * Real.log (N : ℝ)) / ((k : ℝ) + 3) := by ring
  rw [he]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 3)).mpr
  linarith only [hlog]

theorem logarithmic_point_count (k : ℕ) (hk : 1 ≤ k) (N : ℕ) (hN : 0 < N)
    (hlog : Real.log (N : ℝ) ≤ k) (ψ : Fin 2 → ℝ → ℝ)
    (hψ : ∀ i, ContDiffOn ℝ ∞ (ψ i) (Ioo (0 : ℝ) 1))
    (hjet : UnitJets (Fintype.card (Index k) - 1) ψ)
    (hpoly : ∀ Q : MvPolynomial (Fin 2) ℝ, Q ≠ 0 → Q.totalDegree ≤ k →
      ∀ S : Finset (Fin 2 → ℝ),
        (∀ w ∈ S, (∃ t ∈ Ioo (0 : ℝ) 1, (fun i ↦ ψ i t) = w) ∧ eval w Q = 0) →
          S.card < Fintype.card (Index k))
    (S : Finset (Fin 2 → ℝ))
    (hS : ∀ w ∈ S, ∃ t ∈ Ioo (0 : ℝ) 1, (fun i ↦ ψ i t) = w)
    (hgrid : ∀ w ∈ S, ∃ z : Fin 2 → ℤ, ∀ i, w i = (z i : ℝ) / N) :
    (S.card : ℝ) ≤ 32 * Real.exp 4 * ((k + 1 : ℕ) : ℝ) ^ 8 := by
  have hh := point_count k hk N hN ψ hψ hjet hpoly S hS hgrid
  have hp := mul_le_mul_of_nonneg_left (logarithmic_power_bound k N hN hlog)
    (show (0 : ℝ) ≤ 32 * ((k + 1 : ℕ) : ℝ) ^ 8 by positivity)
  exact hh.trans (hp.trans_eq (by ring))

end PaperP1.SimplifiedUnitMapGridCount
