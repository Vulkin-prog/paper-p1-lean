module

public import PaperP1.Algebra.SmallIntegerKernel

/-! # Explicit bounded integer kernel vectors when there is one more column than rows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallIntegerKernelCodimensionOne

open Finset

theorem power_capacity (t H : ℕ) (hH : 0 < H) :
    (2 * ((t + 1) * H * (3 * (t + 1) * H) ^ t) + 1) ^ t <
      ((3 * (t + 1) * H) ^ t + 1) ^ (t + 1) := by
  let D := 3 * (t + 1) * H
  let M := D ^ t
  have hD : 0 < D := by dsimp [D]; positivity
  have hM : 0 < M := pow_pos hD _
  have hprod : 1 ≤ (t + 1) * H * M :=
    Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos (by omega) hH) hM)
  have hbase : 2 * ((t + 1) * H * M) + 1 ≤ D * M := by
    calc
      _ ≤ 3 * ((t + 1) * H * M) := by omega
      _ = D * M := by simp only [D, mul_assoc]
  have hDM : D * M = D ^ (t + 1) := by
    change D * D ^ t = D ^ (t + 1)
    rw [pow_succ, mul_comm]
  change (2 * ((t + 1) * H * M) + 1) ^ t < (M + 1) ^ (t + 1)
  calc
    _ ≤ (D * M) ^ t := Nat.pow_le_pow_left hbase t
    _ = D ^ ((t + 1) * t) := by rw [hDM, ← pow_mul]
    _ = M ^ (t + 1) := by dsimp only [M]; rw [← pow_mul, Nat.mul_comm]
    _ < _ := Nat.pow_lt_pow_left (Nat.lt_succ_self M) (by omega)

theorem exists_small_kernel (t H : ℕ) (hH : 0 < H)
    (A : Fin t → Fin (t + 1) → ℤ) (hA : ∀ j i, |A j i| ≤ (H : ℤ)) :
    ∃ w : Fin (t + 1) → ℤ, w ≠ 0 ∧
      (∀ i, |w i| ≤ ((3 * (t + 1) * H) ^ t : ℕ)) ∧ ∀ j, ∑ i, A j i * w i = 0 :=
  SmallIntegerKernel.exists_of_capacity H ((3 * (t + 1) * H) ^ t) A hA (power_capacity t H hH)

theorem exists_small_kernel_equiv {κ : Type*} [Fintype κ] (t H : ℕ) (hH : 0 < H)
    (e : κ ≃ Fin (t + 1)) (A : Fin t → κ → ℤ) (hA : ∀ j i, |A j i| ≤ (H : ℤ)) :
    ∃ w : κ → ℤ, w ≠ 0 ∧ (∀ i, |w i| ≤ ((3 * (t + 1) * H) ^ t : ℕ)) ∧
      ∀ j, ∑ i, A j i * w i = 0 := by
  obtain ⟨w, hw0, hw, hker⟩ := exists_small_kernel t H hH (fun j i ↦ A j (e.symm i))
    (fun j i ↦ hA j (e.symm i))
  refine ⟨fun i ↦ w (e i), ?_, fun i ↦ hw (e i), ?_⟩
  · intro hz
    apply hw0
    funext i
    simpa only [e.apply_symm_apply, Pi.zero_apply] using congrFun hz (e.symm i)
  · intro j
    calc
      (∑ i, A j i * w (e i)) = ∑ i, A j (e.symm i) * w i :=
        Fintype.sum_equiv e _ _ (fun i ↦ by rw [e.symm_apply_apply])
      _ = 0 := hker j

end PaperP1.SmallIntegerKernelCodimensionOne
