module

public import PaperP1.Arithmetic.TwoWindowComponentSizeBudget
public import PaperP1.Asymptotics.WeakPairActivity

/-! # Uniform powers of the actual full value kernel, with small components accounted for -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalPairKernelPowers

open Finset PaperP1.Arithmetic PaperP1.LargePrimeGraphResolution
  PaperP1.LargePrimeComponentArithmetic PaperP1.RawPairRelationRank

theorem defects_small (C δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x ∈ Model.dyadicBlock N, ∀ y ∈ Model.dyadicBlock N,
        (defectiveVertexCount x y L : ℝ) ≤ δ * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨K, _hK, hdef⟩ := defectiveVertexCount_critical_bound
  obtain ⟨Nd, hd⟩ := hdef C
  obtain ⟨B₀, hb⟩ := ElementaryLogGrowth.log_ge_eventually (K / δ)
  obtain ⟨Ng, hg⟩ := CriticalWindowGeometry.uniform_geometry C B₀
  refine ⟨max Nd Ng, ?_⟩
  intro N hN L hcrit x hx y hy
  have hgeom := hg N (by omega) L hcrit
  have hlog := (div_le_iff₀ hδ).mp (hb (L + 1) hgeom.2.1).1
  have hlogpos : 0 < Real.log ((L + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < L + 1 by have := hgeom.2.2.1; omega))
  have hcoef : K / Real.log ((L + 1 : ℕ) : ℝ) ≤ δ :=
    (div_le_iff₀ hlogpos).mpr (by nlinarith only [hlog])
  calc
    _ ≤ K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) := hd N (by omega) L hcrit x hx y hy
    _ = (K / Real.log ((L + 1 : ℕ) : ℝ)) * ((L + 1 : ℕ) : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)

theorem power_of_rank (C a R ε : ℝ) (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L d : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (d : ℝ) ≤ (a + ε / 2) * ((L + 1 : ℕ) : ℝ) + R →
        (2 ^ d : ℝ) ≤ (N : ℝ) ^ (a + ε) := by
  let b := a + ε / 2
  let K := (2 : ℝ) ^ (b + R) * (2 : ℝ) ^ (b * C)
  obtain ⟨Na, habsorb⟩ := HalfCountSchedule.factor_absorption K b (ε / 2) (by positivity)
  refine ⟨max 2 Na, ?_⟩
  intro N hN L d hcrit hrank
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hpower := WeakPairActivityAsymptotic.critical_binary_power (by omega) hcrit b hb
  have hbound : (2 ^ d : ℝ) ≤ (2 : ℝ) ^ (b + R) * (2 : ℝ) ^ (b * L) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    simp only [Nat.cast_add, Nat.cast_one] at hrank
    dsimp [b] at *
    linarith
  calc
    _ ≤ (2 : ℝ) ^ (b + R) * (2 : ℝ) ^ (b * L) := hbound
    _ ≤ (2 : ℝ) ^ (b + R) * ((2 : ℝ) ^ (b * C) * (N : ℝ) ^ b) :=
      mul_le_mul_of_nonneg_left hpower (Real.rpow_nonneg (by norm_num) _)
    _ = K * (N : ℝ) ^ b := by dsimp [K]; ring
    _ ≤ (N : ℝ) ^ (b + ε / 2) := habsorb N (by omega)
    _ = _ := by congr 1; dsimp [b]; ring

theorem uniform_global (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x ∈ Model.dyadicBlock N, ∀ y ∈ Model.dyadicBlock N,
        (2 ^ fullRank x y L : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
  obtain ⟨Nd, hd⟩ := defects_small C (ε / 2) (by positivity)
  obtain ⟨Np, hp⟩ := power_of_rank C 1 0 ε (by norm_num) hε
  refine ⟨max 2 (max Nd Np), ?_⟩
  intro N hN L hcrit x hx y hy
  have hxpos : 1 ≤ x := by have := (mem_Ico.mp hx).1; omega
  have hypos : 1 ≤ y := by have := (mem_Ico.mp hy).1; omega
  have hr := rank_le_components (L := L) hxpos hypos
  have hb := defectiveVertex_add_twice_nontrivial_le (L := L) hxpos hypos
  have hrR : (fullRank x y L : ℝ) ≤ defectiveVertexCount x y L + nontrivialComponentCount x y L := by exact_mod_cast hr
  have hbR : (defectiveVertexCount x y L : ℝ) + 2 * nontrivialComponentCount x y L ≤ 2 * ((L + 1 : ℕ) : ℝ) := by exact_mod_cast hb
  have hdR := hd N (by omega) L hcrit x hx y hy
  apply hp N (by omega) L (fullRank x y L) hcrit
  nlinarith only [hrR, hbR, hdR, Nat.cast_nonneg (α := ℝ) (defectiveVertexCount x y L)]

theorem uniform_few_small (C ε : ℝ) (k₁ k₂ : ℕ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x ∈ Model.dyadicBlock N, ∀ y ∈ Model.dyadicBlock N,
      (DegreeOneGraphHostCount.components x y L 1).card ≤ k₁ →
      (DegreeOneGraphHostCount.components x y L 2).card ≤ k₂ →
      (DegreeOneGraphHostCount.components y x L 2).card ≤ k₂ →
        (2 ^ fullRank x y L : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨Nd, hd⟩ := defects_small C (ε / 2) (by positivity)
  obtain ⟨Np, hp⟩ := power_of_rank C (1 / 2) ((k₁ : ℝ) + k₂) ε (by norm_num) hε
  refine ⟨max 2 (max Nd Np), ?_⟩
  intro N hN L hcrit x hx y hy ht₁ ht₂ ht₂'
  have hxpos : 1 ≤ x := by have := (mem_Ico.mp hx).1; omega
  have hypos : 1 ≤ y := by have := (mem_Ico.mp hy).1; omega
  have hr := TwoWindowComponentSizeBudget.full_rank_bound (L := L) hxpos hypos
  have hrR : 4 * (fullRank x y L : ℝ) ≤ 4 * defectiveVertexCount x y L + 2 * ((L + 1 : ℕ) : ℝ) +
      2 * (DegreeOneGraphHostCount.components x y L 1).card +
      (DegreeOneGraphHostCount.components x y L 2).card + (DegreeOneGraphHostCount.components y x L 2).card := by exact_mod_cast hr
  have ht₁R : ((DegreeOneGraphHostCount.components x y L 1).card : ℝ) ≤ k₁ := by exact_mod_cast ht₁
  have ht₂R : ((DegreeOneGraphHostCount.components x y L 2).card : ℝ) ≤ k₂ := by exact_mod_cast ht₂
  have ht₂'R : ((DegreeOneGraphHostCount.components y x L 2).card : ℝ) ≤ k₂ := by exact_mod_cast ht₂'
  have hdR := hd N (by omega) L hcrit x hx y hy
  apply hp N (by omega) L (fullRank x y L) hcrit
  nlinarith only [hrR, ht₁R, ht₂R, ht₂'R, hdR, Nat.cast_nonneg (α := ℝ) k₁, Nat.cast_nonneg (α := ℝ) k₂]

end PaperP1.CriticalPairKernelPowers
