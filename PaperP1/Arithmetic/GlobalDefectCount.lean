module

public import PaperP1.Arithmetic.LargeOddKernel
public import PaperP1.Arithmetic.WeightedDefectCounting
public import PaperP1.Analysis.SmoothEulerProduct
public import PaperP1.Asymptotics.ExpSqrtLog
public import PaperP1.Asymptotics.UniformReal

@[expose] public section

/-! # Global counts of the actual positive defective integers -/

namespace PaperP1.GlobalDefectCount

open Finset DefectCounting DefectivePredicate

/-- The actual positive defective integers up to X. -/
noncomputable def positiveDefectsBelow (H X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter (HDefective H)

theorem mem_positiveDefectsBelow {H X n : ℕ} :
    n ∈ positiveDefectsBelow H X ↔ n ≠ 0 ∧ n ≤ X ∧ HDefective H n := by
  classical
  simp [positiveDefectsBelow, Nat.one_le_iff_ne_zero, and_assoc]

theorem mem_positiveDefectsBelow_iff_largeOddKernel {H X n : ℕ} :
    n ∈ positiveDefectsBelow H X ↔
      n ≠ 0 ∧ n ≤ X ∧ LargeOddKernel.largeOddKernel H n = 1 := by
  rw [mem_positiveDefectsBelow, LargeOddKernel.largeOddKernel_eq_one_iff]

/-- Exact positive-integer interpretation of a real counting endpoint,
including negative endpoints, for which the set is empty. -/
theorem mem_positiveDefectsBelow_real_height {H n : ℕ} {Y : ℝ} :
    n ∈ positiveDefectsBelow H ⌊Y⌋₊ ↔
      n ≠ 0 ∧ (n : ℝ) ≤ Y ∧ HDefective H n := by
  rw [mem_positiveDefectsBelow]
  constructor
  · rintro ⟨hn0, hnY, hdef⟩
    exact ⟨hn0, (Nat.le_floor_iff' hn0).mp hnY, hdef⟩
  · rintro ⟨hn0, hnY, hdef⟩
    exact ⟨hn0, Nat.le_floor hnY, hdef⟩

theorem positiveDefectsBelow_eq_represented (H X : ℕ) :
    positiveDefectsBelow H X =
      WeightedDefectCounting.positiveDefectValues (smallPrimesUpTo H) X := by
  classical
  ext n
  rw [mem_positiveDefectsBelow, WeightedDefectCounting.mem_positiveDefectValues_iff]
  constructor
  · rintro ⟨hn0, hnX, hdef⟩
    have hmem := mem_defectValues_of_HDefectRepresentation
      (representationOfHDefective hdef hn0) hnX
    exact ⟨hn0, mem_defectValues_iff.mp hmem⟩
  · rintro ⟨hn0, hnX, S, hS, a, _ha, heq⟩
    exact ⟨hn0, hnX, hDefective_of_HDefectRepresentation
      (⟨S, hS, a, heq⟩ : HDefectRepresentation H n)⟩

/-- Exact finite Euler-product majorant for the intrinsic defective set. -/
theorem card_positiveDefectsBelow_le_sqrt_exp (H X : ℕ) :
    ((positiveDefectsBelow H X).card : ℝ) ≤
      Real.sqrt X * Real.exp (2 * Real.sqrt H) := by
  rw [positiveDefectsBelow_eq_represented]
  exact (WeightedDefectCounting.card_positiveHDefectValues_cast_le_eulerProduct H X).trans
    (mul_le_mul_of_nonneg_left
      (prod_smallPrimesUpTo_one_add_inv_sqrt_le H) (Real.sqrt_nonneg X))

/-- The global N^(1/2+o(1)) conclusion of companion T1.3, uniformly for
every cutoff H ≤ D log N and integral counting height X ≤ C N. -/
theorem global_defect_count_le_rpow_eventually
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H X : ℕ,
      (H : ℝ) ≤ D * Real.log N → (X : ℝ) ≤ C * N →
      ((positiveDefectsBelow H X).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) := by
  have hsub : UniformSubpolynomialOn
      (fun N H => (H : ℝ) ≤ D * Real.log N)
      (fun _ H => Real.sqrt C * Real.exp (2 * Real.sqrt H)) :=
    ExpSqrtLog.uniformSubpolynomialOn_const_mul _
      (ExpSqrtLog.uniformSubpolynomialOn_exp_sqrt_of_le_log
        _ (fun _ H => H) 2 D (by norm_num) hD (fun _ _ h => h))
  obtain ⟨Nsub, hNsub⟩ := UniformReal.uniformSubpolynomialOn_le_rpow hsub ε hε
  refine ⟨max Nsub 1, ?_⟩
  intro N hN H X hH hX
  have hNone : 1 ≤ N := (le_max_right Nsub 1).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfactor : Real.sqrt C * Real.exp (2 * Real.sqrt H) ≤ (N : ℝ) ^ ε :=
    (le_abs_self _).trans (hNsub N ((le_max_left _ _).trans hN) H hH)
  have hsqrt : Real.sqrt (X : ℝ) ≤ Real.sqrt C * Real.sqrt (N : ℝ) := by
    calc
      _ ≤ Real.sqrt (C * N) := Real.sqrt_le_sqrt hX
      _ = _ := Real.sqrt_mul hC _
  calc
    _ ≤ Real.sqrt X * Real.exp (2 * Real.sqrt H) :=
      card_positiveDefectsBelow_le_sqrt_exp H X
    _ ≤ (Real.sqrt C * Real.sqrt N) * Real.exp (2 * Real.sqrt H) :=
      mul_le_mul_of_nonneg_right hsqrt (Real.exp_nonneg _)
    _ = Real.sqrt N * (Real.sqrt C * Real.exp (2 * Real.sqrt H)) := by ring
    _ ≤ Real.sqrt N * (N : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_left hfactor (Real.sqrt_nonneg N)
    _ = (N : ℝ) ^ (1 / 2 + ε) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hNpos]

end PaperP1.GlobalDefectCount

