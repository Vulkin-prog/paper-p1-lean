module

public import PaperP1.Model.ProjectedSplitTuples
public import PaperP1.Asymptotics.ShortSplitLpBounds

/-! # Uniform old-space projection counts for fixed short motifs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedProjectedMotifs

open scoped ENNReal
open Finset MeasureTheory PaperP1.ProjectedSplitTuples
open PaperP1.ShortSplitMoments PaperP1.Model.InfiniteRademacher

theorem exists_even_order (r : ℕ) (E ε : ℝ) (hε : 0 < ε) :
    ∃ v : ℕ, 2 ≤ v ∧ Even v ∧ (r : ℝ) < v ∧ E * r * Real.log 2 / (v : ℝ) ≤ ε / 2 := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max (r : ℝ) (max 1 (2 * E * r * Real.log 2 / ε)))
  let v := 2 * (k + 1)
  have hvr : (0 : ℝ) < v := by dsimp [v]; positivity
  have hkv : (k : ℝ) < v := by dsimp [v]; push_cast; nlinarith
  have hr : (r : ℝ) < v := (lt_of_le_of_lt (le_max_left _ _) hk).trans hkv
  have htarget : 2 * E * r * Real.log 2 / ε ≤ (v : ℝ) := by
    exact ((le_max_right (r : ℝ) _).trans' (le_max_right 1 _)).trans (hk.trans hkv).le
  have hbudget := (div_le_iff₀ hε).mp htarget
  refine ⟨v, by dsimp [v]; omega, ⟨k + 1, by dsimp [v]; omega⟩, hr, ?_⟩
  apply (div_le_iff₀ hvr).mpr
  nlinarith only [hbudget]

theorem old_factor_bound (N r v : ℕ) (hN : 2 ≤ N) (hv : 0 < v) (E ε : ℝ)
    (hrate : E * r * Real.log 2 / (v : ℝ) ≤ ε / 2)
    (O : Finset ℕ) (hO : (O.card : ℝ) ≤ E * Real.log N) :
    ((2 : ℝ) ^ O.card) ^ (r / (v : ℝ)) ≤ (N : ℝ) ^ (ε / 2) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hrNN : 0 ≤ (r : ℝ) / v := by positivity
  have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos hn]
  apply Real.exp_le_exp.mpr
  calc
    Real.log 2 * ((O.card : ℝ) * ((r : ℝ) / v)) ≤
        Real.log 2 * ((E * Real.log N) * ((r : ℝ) / v)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hO hrNN) hlog2
    _ = Real.log N * (E * r * Real.log 2 / (v : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hrate hlogN

theorem fixed_motif_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ a b : ℝ, 0 < a → ∀ D A₀ : ℝ,
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, ∀ O : Finset ℕ, ∀ A : ι → Finset ℤ, ∀ S : ι → Finset ℕ,
        0 < W → (W : ℝ) ≤ D * (Real.log N) ^ A₀ → (O.card : ℝ) ≤ E * Real.log N →
        (∀ i, Even (A i).card ∧ 2 ≤ (A i).card ∧
          ((A i).card : ℝ) ≤ c * Real.log (Real.log N) ∧ ∀ x ∈ A i, x.natAbs ≤ W) →
        (∀ i, ∀ n ∈ S i, a * N ≤ n ∧ (n : ℝ) ≤ b * N) →
        ((tuples O A S).card : ℝ) ≤ (N : ℝ) ^ (Fintype.card ι / 2 + ε) := by
  classical
  let r := Fintype.card ι
  obtain ⟨v, hv, heven, hrv, hrate⟩ := exists_even_order r E ε hε
  have hvr : (0 : ℝ) < v := by exact_mod_cast (show 0 < v by omega)
  let δ := ε / (2 * (r + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨c, hc, hsmall⟩ := PaperP1.ShortSplitLpBounds.small_c_lpNorm v hv heven δ hδ
  refine ⟨c, hc, ?_⟩
  intro a b ha D A₀
  obtain ⟨Np, hNp⟩ := hsmall a b ha D A₀
  refine ⟨max 2 Np, ?_⟩
  intro N hN W O A S hW hwidth hO hA hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hdiff : 0 < (v : ℝ) - r := by linarith
  let p := (v : ℝ) / ((v : ℝ) - r)
  have hp : 0 < p := div_pos hvr hdiff
  have hbalance : 1 / p + Fintype.card ι / (v : ℝ) = 1 := by
    dsimp [p, r]
    field_simp; ring
  have hcount := fixed_motif_holder O A S p hp v (by omega) hbalance
  have hLp : ∀ i, lpNorm (sumValue (A i) (S i)) (v : ℝ≥0∞) infiniteRademacherMeasure ≤ (N : ℝ) ^ (1 / 2 + δ) := by
    intro i
    exact (hNp N (by omega) W (A i) hW (hA i).1 (hA i).2.1 hwidth (hA i).2.2.1
      (hA i).2.2.2 (S i) (hS i)).1
  have hprod : (∏ i, lpNorm (sumValue (A i) (S i)) (v : ℝ≥0∞) infiniteRademacherMeasure) ≤
      ((N : ℝ) ^ (1 / 2 + δ)) ^ r := by
    calc
      _ ≤ ∏ _i : ι, (N : ℝ) ^ (1 / 2 + δ) := prod_le_prod₀ (fun _ _ ↦ lpNorm_nonneg) (fun i _ ↦ hLp i)
      _ = _ := by simp only [prod_const, card_univ, r]
  have hfactor := old_factor_bound N r v (by omega) (by omega) E ε hrate O hO
  have hδeq : δ * (2 * (r + 1)) = ε := by dsimp [δ]; field_simp
  have hδr : δ * r ≤ ε / 2 := by nlinarith only [hδeq, hδ]
  calc
    _ ≤ ((2 : ℝ) ^ O.card) ^ (r / (v : ℝ)) *
        ∏ i, lpNorm (sumValue (A i) (S i)) (v : ℝ≥0∞) infiniteRademacherMeasure := hcount
    _ ≤ (N : ℝ) ^ (ε / 2) * ((N : ℝ) ^ (1 / 2 + δ)) ^ r :=
      mul_le_mul hfactor hprod (prod_nonneg fun _ _ ↦ lpNorm_nonneg) (Real.rpow_nonneg hn.le _)
    _ = (N : ℝ) ^ (ε / 2 + (1 / 2 + δ) * r) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_add hn]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [r] at hδr ⊢; nlinarith only [hδr])

end PaperP1.FixedProjectedMotifs
