module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-! # Explicit pigeonhole bounds for nonzero small integer vectors in a matrix kernel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallIntegerKernel

open Finset

def positiveBox (n M : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun _ ↦ Icc 0 (M : ℤ))

def symmetricBox (t R : ℕ) : Finset (Fin t → ℤ) :=
  Fintype.piFinset (fun _ ↦ Icc (-(R : ℤ)) (R : ℤ))

def evaluation {n t : ℕ} (A : Fin t → Fin n → ℤ) (v : Fin n → ℤ) : Fin t → ℤ :=
  fun j ↦ ∑ i, A j i * v i

theorem positiveBox_card (n M : ℕ) : (positiveBox n M).card = (M + 1) ^ n := by
  rw [positiveBox, Fintype.card_piFinset_const, Int.card_Icc]
  simp

theorem symmetricBox_card (t R : ℕ) : (symmetricBox t R).card = (2 * R + 1) ^ t := by
  rw [symmetricBox, Fintype.card_piFinset_const, Int.card_Icc]
  have he : (R : ℤ) + 1 - -(R : ℤ) = (2 * R + 1 : ℕ) := by push_cast; ring
  rw [he, Int.toNat_natCast]

theorem evaluation_mem {n t : ℕ} (H M : ℕ) (A : Fin t → Fin n → ℤ)
    (hA : ∀ j i, |A j i| ≤ (H : ℤ)) (v : Fin n → ℤ) (hv : v ∈ positiveBox n M) :
    evaluation A v ∈ symmetricBox t (n * H * M) := by
  have hv' : ∀ i, 0 ≤ v i ∧ v i ≤ (M : ℤ) := by
    simpa only [positiveBox, Fintype.mem_piFinset, mem_Icc] using hv
  rw [symmetricBox, Fintype.mem_piFinset]
  intro j
  apply mem_Icc.mpr
  apply abs_le.mp
  calc
    |evaluation A v j| ≤ ∑ i, |A j i * v i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (H : ℤ) * M := by
      apply sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hv' i).1]
      exact mul_le_mul (hA j i) (hv' i).2 (hv' i).1 (by positivity)
    _ = (n * H * M : ℕ) := by
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, mul_assoc]

theorem exists_of_capacity {n t : ℕ} (H M : ℕ) (A : Fin t → Fin n → ℤ)
    (hA : ∀ j i, |A j i| ≤ (H : ℤ))
    (hcapacity : (2 * (n * H * M) + 1) ^ t < (M + 1) ^ n) :
    ∃ w : Fin n → ℤ, w ≠ 0 ∧ (∀ i, |w i| ≤ (M : ℤ)) ∧ ∀ j, ∑ i, A j i * w i = 0 := by
  have hc : (symmetricBox t (n * H * M)).card < (positiveBox n M).card := by
    rw [positiveBox_card, symmetricBox_card]
    exact hcapacity
  obtain ⟨u, hu, v, hv, hne, heq⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hc
    (fun v hv ↦ evaluation_mem H M A hA v hv)
  have hu' : ∀ i, 0 ≤ u i ∧ u i ≤ (M : ℤ) := by
    simpa only [positiveBox, Fintype.mem_piFinset, mem_Icc] using hu
  have hv' : ∀ i, 0 ≤ v i ∧ v i ≤ (M : ℤ) := by
    simpa only [positiveBox, Fintype.mem_piFinset, mem_Icc] using hv
  refine ⟨fun i ↦ u i - v i, ?_, ?_, ?_⟩
  · intro hw
    apply hne
    funext i
    have h := congrFun hw i
    exact sub_eq_zero.mp h
  · intro i
    exact abs_le.mpr ⟨by linarith only [(hu' i).1, (hv' i).2],
      by linarith only [(hu' i).2, (hv' i).1]⟩
  · intro j
    simp_rw [mul_sub]
    rw [sum_sub_distrib]
    exact sub_eq_zero.mpr (congrFun heq j)

theorem power_capacity (n t H : ℕ) (hn : 0 < n) (hH : 0 < H) (hdim : 8 * t ≤ 7 * n) :
    (2 * (n * H * (3 * n * H) ^ 7) + 1) ^ t < ((3 * n * H) ^ 7 + 1) ^ n := by
  let D := 3 * n * H
  let M := D ^ 7
  have hD : 0 < D := by dsimp [D]; positivity
  have hM : 0 < M := pow_pos hD _
  have hprod : 1 ≤ n * H * M := Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos hn hH) hM)
  have hbase : 2 * (n * H * M) + 1 ≤ D * M := by
    calc
      _ ≤ 3 * (n * H * M) := by omega
      _ = D * M := by simp only [D, mul_assoc]
  have hDM : D * M = D ^ 8 := by
    change D * D ^ 7 = D ^ 8
    rw [pow_succ D 7, mul_comm]
  change (2 * (n * H * M) + 1) ^ t < (M + 1) ^ n
  calc
    _ ≤ (D * M) ^ t := Nat.pow_le_pow_left hbase t
    _ = D ^ (8 * t) := by rw [hDM, ← pow_mul]
    _ ≤ D ^ (7 * n) := Nat.pow_le_pow_right hD hdim
    _ = M ^ n := pow_mul D 7 n
    _ < _ := Nat.pow_lt_pow_left (Nat.lt_succ_self M) hn.ne'

theorem exists_small_kernel {n t : ℕ} (H : ℕ) (hn : 0 < n) (hH : 0 < H)
    (hdim : 8 * t ≤ 7 * n) (A : Fin t → Fin n → ℤ) (hA : ∀ j i, |A j i| ≤ (H : ℤ)) :
    ∃ w : Fin n → ℤ, w ≠ 0 ∧ (∀ i, |w i| ≤ ((3 * n * H) ^ 7 : ℕ)) ∧
      ∀ j, ∑ i, A j i * w i = 0 :=
  exists_of_capacity H ((3 * n * H) ^ 7) A hA (power_capacity n t H hn hH hdim)

end PaperP1.SmallIntegerKernel
