module

public import PaperP1.Algebra.SmallIntegerKernel

/-! # Bounded integer kernel vectors for every strict row-column dimension gap -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallIntegerKernelRankGap

theorem power_capacity (n t H : ℕ) (hn : 0 < n) (hH : 0 < H) (ht : t < n) :
    (2 * (n * H * (3 * n * H) ^ t) + 1) ^ t < ((3 * n * H) ^ t + 1) ^ n := by
  let D := 3 * n * H
  let M := D ^ t
  have hD : 0 < D := by dsimp [D]; positivity
  have hM : 0 < M := pow_pos hD _
  have hprod : 1 ≤ n * H * M := Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos hn hH) hM)
  have hbase : 2 * (n * H * M) + 1 ≤ D * M := by
    calc
      _ ≤ 3 * (n * H * M) := by omega
      _ = _ := by dsimp [D]; ring
  have hDM : D * M = D ^ (t + 1) := by
    change D * D ^ t = D ^ (t + 1)
    rw [pow_succ, mul_comm]
  change (2 * (n * H * M) + 1) ^ t < (M + 1) ^ n
  calc
    _ ≤ (D * M) ^ t := Nat.pow_le_pow_left hbase t
    _ = D ^ ((t + 1) * t) := by rw [hDM, ← pow_mul]
    _ ≤ D ^ (n * t) := Nat.pow_le_pow_right hD (Nat.mul_le_mul_right t (by omega : t + 1 ≤ n))
    _ = M ^ n := by dsimp [M]; rw [← pow_mul, Nat.mul_comm]
    _ < _ := Nat.pow_lt_pow_left (Nat.lt_succ_self M) hn.ne'

theorem exists_small_kernel {n t : ℕ} (H : ℕ) (hn : 0 < n) (hH : 0 < H) (ht : t < n)
    (A : Fin t → Fin n → ℤ) (hA : ∀ j i, |A j i| ≤ (H : ℤ)) :
    ∃ w : Fin n → ℤ, w ≠ 0 ∧ (∀ i, |w i| ≤ ((3 * n * H) ^ t : ℕ)) ∧
      ∀ j, ∑ i, A j i * w i = 0 :=
  SmallIntegerKernel.exists_of_capacity H ((3 * n * H) ^ t) A hA (power_capacity n t H hn hH ht)

theorem exists_uniform_small_kernel {n t : ℕ} (H : ℕ) (hn : 0 < n) (hH : 0 < H) (ht : t < n)
    (A : Fin t → Fin n → ℤ) (hA : ∀ j i, |A j i| ≤ (H : ℤ)) :
    ∃ w : Fin n → ℤ, w ≠ 0 ∧ (∀ i, |w i| ≤ ((3 * n * H) ^ (n - 1) : ℕ)) ∧
      ∀ j, ∑ i, A j i * w i = 0 := by
  obtain ⟨w, hw, hbound, hzero⟩ := exists_small_kernel H hn hH ht A hA
  refine ⟨w, hw, ?_, hzero⟩
  intro i
  apply (hbound i).trans
  exact_mod_cast Nat.pow_le_pow_right (by positivity : 0 < 3 * n * H) (by omega : t ≤ n - 1)

theorem exists_uniform_small_kernel_equiv {κ : Type*} [Fintype κ] (n t H : ℕ)
    (hn : 0 < n) (hH : 0 < H) (ht : t < n) (e : κ ≃ Fin n)
    (A : Fin t → κ → ℤ) (hA : ∀ j i, |A j i| ≤ (H : ℤ)) :
    ∃ w : κ → ℤ, w ≠ 0 ∧ (∀ i, |w i| ≤ ((3 * n * H) ^ (n - 1) : ℕ)) ∧
      ∀ j, ∑ i, A j i * w i = 0 := by
  obtain ⟨w, hw0, hw, hker⟩ := exists_uniform_small_kernel H hn hH ht
    (fun j i ↦ A j (e.symm i)) (fun j i ↦ hA j (e.symm i))
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

end PaperP1.SmallIntegerKernelRankGap
