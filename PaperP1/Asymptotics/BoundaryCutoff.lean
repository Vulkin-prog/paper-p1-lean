module

public import PaperP1.Combinatorics.LargeSubsetWeights
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! # The actual least stopping cutoff in companion Section T12 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundaryCutoff

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def Condition (Λ : ℝ) (N K : ℕ) : Prop :=
  max 4 ⌈4 * Real.exp 1 * Λ⌉₊ ≤ K ∧
    3 * Real.log N ≤ (K : ℝ) * Real.log ((K : ℝ) / (2 * Real.exp 1 * Λ))

theorem condition_exists (Λ : ℝ) (hΛ : 0 < Λ) (N : ℕ) : ∃ K : ℕ, Condition Λ N K := by
  let M : ℝ := max ((max 4 ⌈4 * Real.exp 1 * Λ⌉₊ : ℕ) : ℝ)
    (max (2 * Real.exp 2 * Λ) (3 * Real.log N))
  let K : ℕ := ⌈M⌉₊
  have hM : M ≤ (K : ℝ) := Nat.le_ceil M
  have hinit : ((max 4 ⌈4 * Real.exp 1 * Λ⌉₊ : ℕ) : ℝ) ≤ K := (le_max_left _ _).trans hM
  have hbig : 2 * Real.exp 2 * Λ ≤ (K : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hM)
  have hlogN : 3 * Real.log N ≤ (K : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hM)
  have hexp : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  have hratio : Real.exp 1 ≤ (K : ℝ) / (2 * Real.exp 1 * Λ) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.exp 1 * Λ)).mpr
    have heq : Real.exp 1 * (2 * Real.exp 1 * Λ) = 2 * Real.exp 2 * Λ := by rw [hexp]; ring
    exact heq.le.trans hbig
  have hlog : 1 ≤ Real.log ((K : ℝ) / (2 * Real.exp 1 * Λ)) := by
    have h := Real.log_le_log (Real.exp_pos 1) hratio
    simpa only [Real.log_exp] using h
  refine ⟨K, ?_, ?_⟩
  · exact_mod_cast hinit
  · exact hlogN.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg K))

def cutoff (Λ : ℝ) (hΛ : 0 < Λ) (N : ℕ) : ℕ := Nat.find (condition_exists Λ hΛ N)

theorem cutoff_spec (Λ : ℝ) (hΛ : 0 < Λ) (N : ℕ) : Condition Λ N (cutoff Λ hΛ N) :=
  Nat.find_spec (condition_exists Λ hΛ N)

theorem cutoff_minimal (Λ : ℝ) (hΛ : 0 < Λ) (N K : ℕ) (hK : Condition Λ N K) :
    cutoff Λ hΛ N ≤ K := Nat.find_min' (condition_exists Λ hΛ N) hK

theorem cutoff_pos (Λ : ℝ) (hΛ : 0 < Λ) (N : ℕ) : 0 < cutoff Λ hΛ N := by
  have h := (cutoff_spec Λ hΛ N).1
  have hfour : 4 ≤ max 4 ⌈4 * Real.exp 1 * Λ⌉₊ := le_max_left _ _
  omega

theorem cutoff_size (Λ : ℝ) (hΛ : 0 < Λ) (N : ℕ) : 2 * Λ ≤ (cutoff Λ hΛ N : ℝ) := by
  have h := (cutoff_spec Λ hΛ N).1
  have hceil : ⌈4 * Real.exp 1 * Λ⌉₊ ≤ cutoff Λ hΛ N := (le_max_right _ _).trans h
  have hceilR : (⌈4 * Real.exp 1 * Λ⌉₊ : ℝ) ≤ cutoff Λ hΛ N := by exact_mod_cast hceil
  have hraw := (Nat.le_ceil (4 * Real.exp 1 * Λ)).trans hceilR
  have he : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  nlinarith

theorem powerset_tail_bound {ι : Type*} (P : Finset ι) (p Λ : ℝ) (hΛ : 0 < Λ)
    (N : ℕ) (hN : 0 < N) (hp : 0 ≤ p) (hmean : (P.card : ℝ) * p ≤ Λ) :
    PaperP1.LargeSubsetWeights.weightSum P (2 * p) (cutoff Λ hΛ N) ≤ (N : ℝ) ^ (-3 : ℝ) :=
  PaperP1.LargeSubsetWeights.log_budget_bound P p Λ (cutoff Λ hΛ N) N hp hΛ
    (cutoff_pos Λ hΛ N) hN (cutoff_size Λ hΛ N) hmean (cutoff_spec Λ hΛ N).2

end PaperP1.BoundaryCutoff
