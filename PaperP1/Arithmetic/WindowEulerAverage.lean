module

public import PaperP1.Arithmetic.RoughEulerMoments
public import PaperP1.Analysis.FiniteProductPowerMean

/-! # The first moment of the rough-prime window product is linear in the dyadic scale, uniformly in the width -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WindowEulerAverage

open Finset PaperP1.FiniteEulerAverage PaperP1.RoughEulerMoments

def windowProduct (P : Finset ℕ) (B x : ℕ) : ℝ :=
  ∏ i : Fin B, localProduct P halfWeight (x - 1 + i.val)

theorem local_nonneg (P : Finset ℕ) (n : ℕ) : 0 ≤ localProduct P halfWeight n := by
  apply prod_nonneg
  intro p _
  have h : 0 ≤ halfWeight p := Real.rpow_nonneg (Nat.cast_nonneg p) _
  linarith only [h]

theorem window_nonneg (P : Finset ℕ) (B x : ℕ) : 0 ≤ windowProduct P B x :=
  prod_nonneg (fun _ _ ↦ local_nonneg P _)

theorem first_moment (B N : ℕ) (hN : 2 ≤ N) (hB : 1 ≤ B) (hBN : B ≤ N + 1)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (hrough : ∀ p ∈ P, 64 * B ^ 2 < p) :
    (∑ x ∈ Ico N (2 * N), windowProduct P B x) ≤ (3 * N : ℕ) * Real.exp 2 := by
  classical
  let _ : Nonempty (Fin B) := ⟨⟨0, by omega⟩⟩
  have hm (i : Fin B) : (∑ x ∈ Ico N (2 * N), (localProduct P halfWeight (x - 1 + i.val)) ^ B) ≤
      (3 * N : ℕ) * Real.exp 2 := by
    let g := fun x : ℕ ↦ x - 1 + i.val
    have hinj : Set.InjOn g (Ico N (2 * N) : Set ℕ) := by
      intro x hx y hy hxy
      have hx' := (mem_Ico.mp hx).1
      have hy' := (mem_Ico.mp hy).1
      change x - 1 + i.val = y - 1 + i.val at hxy
      omega
    have hsub : (Ico N (2 * N)).image g ⊆ Ioc 0 (3 * N) := by
      intro n hn
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hn
      have hx' := mem_Ico.mp hx
      have hi := i.isLt
      apply mem_Ioc.mpr
      dsimp [g]
      omega
    calc
      _ = ∑ n ∈ (Ico N (2 * N)).image g, (localProduct P halfWeight n) ^ B := (sum_image hinj).symm
      _ ≤ ∑ n ∈ Ioc 0 (3 * N), (localProduct P halfWeight n) ^ B :=
        sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ ↦ pow_nonneg (local_nonneg P n) _)
      _ ≤ _ := moment_bound B hB P hP hrough (3 * N)
  exact FiniteProductPowerMean.sum_product_le_moment (Ico N (2 * N))
    (fun i : Fin B ↦ fun x ↦ localProduct P halfWeight (x - 1 + i.val))
    (fun _ _ _ ↦ local_nonneg P _) _ (fun i ↦ by simpa only [Fintype.card_fin] using hm i)

end PaperP1.WindowEulerAverage
