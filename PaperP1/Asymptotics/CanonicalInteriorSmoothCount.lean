module

public import PaperP1.Asymptotics.CanonicalInteriorCount
public import PaperP1.Combinatorics.FiniteCoverCount

/-! # Sum the actual smooth-part choices in the sharp canonical interior count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CanonicalInteriorSmoothCount

open Finset PaperP1.SmallPrimeBudget PaperP1.LargeOddKernel PaperP1.DefectivePredicate PaperP1.DefectCounting

theorem uniform_count (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
    (δ D K A ε : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 2) (hD : 0 ≤ D) (hK : 0 ≤ K) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H h : ℕ, ∀ T : ℝ,
      (H : ℝ) ≤ D * Real.log N → 0 < h → (h : ℝ) ≤ K * (Real.log N) ^ A → 0 ≤ T →
      ∀ S : Finset ℕ,
      (∀ n ∈ S, 0 < n ∧ N ≤ 2 * n ∧ n ≤ 3 * N ∧ n + h ≤ 4 * N) →
      (∀ n ∈ S, (largeOddKernel H n : ℝ) ≤ T ∧ (largeOddKernel H (n + h) : ℝ) ≤ T) →
      (∀ n ∈ S, 4 * Real.sqrt N < ((canonicalSquarePart n * canonicalSquarePart (n + h) : ℕ) : ℝ) ∧
        4 * (N : ℝ) ^ δ < ((largeOddKernel H n * largeOddKernel H (n + h) : ℕ) : ℝ)) →
      (S.card : ℝ) ≤ (T + (N : ℝ) ^ (7 / 12 : ℝ)) * (N : ℝ) ^ ε := by
  classical
  obtain ⟨Nf, hf⟩ := CanonicalInteriorCount.uniform_fixed_coefficients hHB hNG δ K A (ε / 2)
    hδ hδsmall hK hA (by positivity)
  obtain ⟨Ns, hs⟩ := LogarithmicPrimeCount.smooth_support_count_le_rpow_eventually D hD (ε / 4) (by positivity)
  refine ⟨max 2 (max Nf Ns), ?_⟩
  intro N hN H h T hH hh hshift hT S hheight hkernel hlarge
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let P := (smallPrimesUpTo H).powerset
  let I := P ×ˢ P
  let F := fun w : Finset ℕ × Finset ℕ ↦ S.filter (fun n ↦ smallOddSupport H n = w.1 ∧ smallOddSupport H (n + h) = w.2)
  let B := T + (N : ℝ) ^ (7 / 12 : ℝ)
  have hcover : ∀ n ∈ S, ∃ w ∈ I, n ∈ F w := by
    intro n hnS
    exact ⟨(smallOddSupport H n, smallOddSupport H (n + h)),
      mem_product.mpr ⟨mem_powerset.mpr (smallOddSupport_subset H n), mem_powerset.mpr (smallOddSupport_subset H (n + h))⟩,
      mem_filter.mpr ⟨hnS, rfl, rfl⟩⟩
  have hF : ∀ w ∈ I, ((F w).card : ℝ) ≤ B * (N : ℝ) ^ (ε / 2) := by
    intro w _hw
    apply hf N (by omega) H h (w.1.prod id) (w.2.prod id) T hh hshift hT (F w)
    · exact fun n hnF ↦ hheight n (mem_filter.mp hnF).1
    · intro n hnF
      obtain ⟨_hnS, hs₁, hs₂⟩ := mem_filter.mp hnF
      exact ⟨congrArg (fun s : Finset ℕ ↦ s.prod id) hs₁, congrArg (fun s : Finset ℕ ↦ s.prod id) hs₂⟩
    · exact fun n hnF ↦ hkernel n (mem_filter.mp hnF).1
    · exact fun n hnF ↦ hlarge n (mem_filter.mp hnF).1
  have hP : (P.card : ℝ) ≤ (N : ℝ) ^ (ε / 4) := hs N (by omega) H hH
  have hI : (I.card : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    calc
      _ = (P.card : ℝ) * P.card := by simp only [I, card_product, Nat.cast_mul]
      _ ≤ (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (ε / 4) :=
        mul_le_mul hP hP (Nat.cast_nonneg _) (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  calc
    _ ≤ (I.card : ℝ) * (B * (N : ℝ) ^ (ε / 2)) := FiniteCoverCount.cardinal_le S I F _ hcover hF
    _ ≤ (N : ℝ) ^ (ε / 2) * (B * (N : ℝ) ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_right hI (by dsimp only [B]; positivity)
    _ = _ := by
      calc
        _ = B * ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2)) := by ring
        _ = _ := by rw [← Real.rpow_add hn, add_halves]

end PaperP1.CanonicalInteriorSmoothCount
