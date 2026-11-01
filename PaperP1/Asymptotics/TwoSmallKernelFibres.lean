module

public import PaperP1.Arithmetic.PositiveProductPairs
public import PaperP1.Arithmetic.LogarithmicPrimeCount
public import PaperP1.Diophantine.LinearKernelFibres

/-! # Two small large-prime kernels at fixed distinct offsets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoSmallKernelFibres

open Finset PaperP1.SmallPrimeBudget PaperP1.LinearKernelFibres
  PaperP1.LargeOddKernel PaperP1.DefectCounting

def largeKernel (H n : ℕ) (a : ℤ) : ℕ := largeOddKernel H (value n a)

def support (H n : ℕ) (a : ℤ) : Finset ℕ := smallOddSupport H (value n a)

theorem largeKernel_pos (H n : ℕ) (a : ℤ) : 0 < largeKernel H n a :=
  largeOddKernel_pos H (value n a)

theorem kernel_factorization (H n : ℕ) (a : ℤ) :
    (support H n a).prod id * largeKernel H n a = linearKernel n a :=
  small_mul_large H (value n a)

theorem largeKernel_le (H n : ℕ) (a : ℤ) : largeKernel H n a ≤ linearKernel n a := by
  rw [← kernel_factorization H n a]
  exact Nat.le_mul_of_pos_left _ (smallOddPart_pos H (value n a))

theorem fixed_offsets (D ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H W : ℕ, ∀ Q : ℝ, ∀ a b : ℤ,
      (H : ℝ) ≤ D * Real.log N → 2 * W ≤ N → 0 ≤ Q →
      a.natAbs ≤ W → b.natAbs ≤ W → a ≠ b → ∀ S : Finset ℕ,
      (∀ n ∈ S, N ≤ n ∧ n ≤ 2 * N ∧
        (largeKernel H n a * largeKernel H n b : ℕ) ≤ Q) →
      (S.card : ℝ) ≤ Q * (N : ℝ) ^ ε := by
  let η := ε / 4
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨Np, hNp⟩ := PaperP1.PositiveProductPairs.uniform_count 6 η hη
  obtain ⟨Ns, hNs⟩ := PaperP1.LogarithmicPrimeCount.smooth_support_count_le_rpow_eventually D hD η hη
  obtain ⟨Nf, hNf⟩ := fixed_linear_kernels_count η hη
  refine ⟨max 2 (max Np (max Ns Nf)), ?_⟩
  intro N hN H W Q a b hH hW hQ ha hb hab S hS
  have hNtwo : 2 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let R := S.image fun n ↦ (largeKernel H n a, largeKernel H n b)
  have hR : (R.card : ℝ) ≤ Q * (N : ℝ) ^ η := by
    apply hNp N (by omega) Q hQ R
    intro z hz
    obtain ⟨n, hnS, rfl⟩ := mem_image.mp hz
    have haheight := offset_bounds N n W a hNtwo hW (hS n hnS).1 (hS n hnS).2.1 ha
    have hbheight := offset_bounds N n W b hNtwo hW (hS n hnS).1 (hS n hnS).2.1 hb
    have hka : largeKernel H n a ≤ N ^ 3 :=
      ((largeKernel_le H n a).trans ((kernel_part_le_value n a haheight.1).1.trans haheight.2)).trans
        (height_budget N hNtwo)
    have hkb : largeKernel H n b ≤ N ^ 3 :=
      ((largeKernel_le H n b).trans ((kernel_part_le_value n b hbheight.1).1.trans hbheight.2)).trans
        (height_budget N hNtwo)
    refine ⟨largeKernel_pos H n a, largeKernel_pos H n b, ?_, (hS n hnS).2.2⟩
    calc
      _ ≤ N ^ 3 * N ^ 3 := Nat.mul_le_mul hka hkb
      _ = N ^ 6 := by ring
  let P := (smallPrimesUpTo H).powerset
  let I := (P ×ˢ P) ×ˢ R
  let F := fun w : (Finset ℕ × Finset ℕ) × (ℕ × ℕ) ↦ S.filter fun n ↦
    support H n a = w.1.1 ∧ support H n b = w.1.2 ∧
      largeKernel H n a = w.2.1 ∧ largeKernel H n b = w.2.2
  have hcover : ∀ n ∈ S, ∃ w ∈ I, n ∈ F w := by
    intro n hnS
    refine ⟨((support H n a, support H n b), (largeKernel H n a, largeKernel H n b)), ?_, ?_⟩
    · exact mem_product.mpr ⟨mem_product.mpr
        ⟨mem_powerset.mpr (smallOddSupport_subset H (value n a)),
          mem_powerset.mpr (smallOddSupport_subset H (value n b))⟩,
        mem_image_of_mem _ hnS⟩
    · exact mem_filter.mpr ⟨hnS, rfl, rfl, rfl, rfl⟩
  have hF : ∀ w ∈ I, ((F w).card : ℝ) ≤ (N : ℝ) ^ η := by
    intro w _
    apply hNf N (by omega) W (w.1.1.prod id * w.2.1) (w.1.2.prod id * w.2.2) a b hW ha hb hab
    intro n hnF
    obtain ⟨hnS, hsa, hsb, hka, hkb⟩ := mem_filter.mp hnF
    refine ⟨(hS n hnS).1, (hS n hnS).2.1, ?_, ?_⟩
    · rw [← kernel_factorization H n a, hsa, hka]
    · rw [← kernel_factorization H n b, hsb, hkb]
  have hP : (P.card : ℝ) ≤ (N : ℝ) ^ η := hNs N (by omega) H hH
  have hI : (I.card : ℝ) ≤ (N : ℝ) ^ η * (N : ℝ) ^ η * (Q * (N : ℝ) ^ η) := by
    simp only [I, card_product, Nat.cast_mul]
    exact mul_le_mul (mul_le_mul hP hP (Nat.cast_nonneg _) (Real.rpow_nonneg hn.le _)) hR
      (Nat.cast_nonneg _) (by positivity)
  calc
    _ ≤ (I.card : ℝ) * (N : ℝ) ^ η :=
      PaperP1.FiniteCoverCount.cardinal_le S I F _ hcover hF
    _ ≤ ((N : ℝ) ^ η * (N : ℝ) ^ η * (Q * (N : ℝ) ^ η)) * (N : ℝ) ^ η :=
      mul_le_mul_of_nonneg_right hI (Real.rpow_nonneg hn.le _)
    _ = Q * (N : ℝ) ^ ε := by
      calc
        _ = Q * ((N : ℝ) ^ η * (N : ℝ) ^ η * (N : ℝ) ^ η * (N : ℝ) ^ η) := by ring
        _ = Q * (N : ℝ) ^ (η + η + η + η) := by rw [← Real.rpow_add hn, ← Real.rpow_add hn, ← Real.rpow_add hn]
        _ = _ := by congr 2; dsimp [η]; ring

end PaperP1.TwoSmallKernelFibres
