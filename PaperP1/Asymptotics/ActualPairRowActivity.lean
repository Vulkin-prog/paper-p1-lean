module

public import PaperP1.Model.JointTupleSupport
public import PaperP1.Model.PairRowActivity
public import PaperP1.Asymptotics.FixedSourceMassStep
public import PaperP1.Asymptotics.CriticalActualMean
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # Unconditional subpower actual joint and absolute covariance rows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualPairRowActivity

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PairRowActivity PaperP1.HeterogeneousDirectMaximum

theorem uniform_joint_row (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ dyadicBlock N,
      jointRow (dyadicBlock N) L x ≤ (N : ℝ) ^ ε * infiniteMarginal x L := by
  obtain ⟨NS, hstep⟩ := FixedSourceMassStep.point_step 1 (by decide) C ε hε
  obtain ⟨NG, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 2 (max NS NG), by omega, ?_⟩
  intro N hN L hband x hx
  have hL : 0 < L := by have h := (hgeom N (by omega) L hband).2.2.1; omega
  have h := hstep N (by omega) L hband (fun _ : Fin 1 ↦ x) (fun _ ↦ hx) (fun _ ↦ startRhs L)
  simpa only [jointRow, dyadicBlock, JointTupleSupport.prescribed_eq_support (hL := hL), JointTupleSupport.snoc_one_support,
    JointTupleSupport.constant_one_support, InfiniteTripleCancellation.singleton_joint] using h

theorem uniform_absolute_row (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      ∀ x ∈ dyadicBlock N, absoluteRow G L x ≤ (N : ℝ) ^ ε * infiniteMarginal x L := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  let M : ℝ := 2 * (2 : ℝ) ^ C
  obtain ⟨NQ, _hNQ, hrow⟩ := uniform_joint_row C η hη
  obtain ⟨NM, hNM, hmean⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NA, hA⟩ := HalfCountSchedule.factor_absorption M 0 η hη
  obtain ⟨NB, hB⟩ := HalfCountSchedule.factor_absorption 2 η η hη
  refine ⟨max NM (max NQ (max NA NB)), by omega, ?_⟩
  intro N hN L hband G hG x hx
  have hpx := MissingBlockProbabilities.infiniteMarginal_nonneg x L
  have hmeanG : actualMean G L ≤ M := by
    calc
      _ ≤ actualMean (dyadicBlock N) L := sum_le_sum_of_subset_of_nonneg hG
        (fun y _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg y L)
      _ = CountObservables.countMoment (dyadicBlock N) L 1 := actualMean_eq_countMoment (subset_refl _)
      _ ≤ _ := (hmean N (by omega) L hband).2
  have hm : M ≤ (N : ℝ) ^ η := by
    simpa only [Real.rpow_zero, mul_one, zero_add] using hA N (by omega)
  have hf : 2 * (N : ℝ) ^ η ≤ (N : ℝ) ^ ε := by
    convert hB N (by omega) using 1
    congr 1
    dsimp [η]
    ring
  have hjoint : jointRow G L x ≤ (N : ℝ) ^ η * infiniteMarginal x L :=
    (sum_le_sum_of_subset_of_nonneg hG (fun y _ _ ↦ infiniteJointMoment_nonneg L {x, y})).trans
      (hrow N (by omega) L hband x hx)
  calc
    _ ≤ jointRow G L x + infiniteMarginal x L * actualMean G L := row_bound G L x
    _ ≤ (N : ℝ) ^ η * infiniteMarginal x L + infiniteMarginal x L * M :=
      add_le_add hjoint (mul_le_mul_of_nonneg_left hmeanG hpx)
    _ = infiniteMarginal x L * ((N : ℝ) ^ η + M) := by ring
    _ ≤ infiniteMarginal x L * (2 * (N : ℝ) ^ η) :=
      mul_le_mul_of_nonneg_left (by linarith only [hm]) hpx
    _ ≤ infiniteMarginal x L * (N : ℝ) ^ ε := mul_le_mul_of_nonneg_left hf hpx
    _ = _ := mul_comm _ _

theorem uniform_marginal_cap (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ dyadicBlock N,
      infiniteMarginal x L ≤ (2 * (2 : ℝ) ^ C) / N := by
  obtain ⟨NP, hcap⟩ := TripleRankGeometry.critical_nominal_marginal_cap C
  refine ⟨max 2 NP, by omega, ?_⟩
  intro N hN L hband x hx
  calc
    _ ≤ 2 * (2 ^ L : ℝ)⁻¹ := hcap N (by omega) L hband x hx
    _ ≤ 2 * ((2 : ℝ) ^ C / N) :=
      mul_le_mul_of_nonneg_left (LocalRigidityConsequences.nominal_marginal_bound (by omega) hband) (by norm_num)
    _ = _ := by ring

end PaperP1.ActualPairRowActivity
