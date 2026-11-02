module

public import PaperP1.Arithmetic.PositiveLineSplitProducts
public import PaperP1.Asymptotics.PolynomialSplitKernelCount

/-! # Uniform square-product counts on any positive-slope rational line -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositiveLineSplitCount

open Finset PaperP1.PositiveLineSplitProducts PaperP1.LinearKernelFibres

theorem uniform_count (K d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ a b : ℕ, 0 < a → 0 < b → ∀ c : ℤ,
      ∀ P Q : Finset ℤ, P.Nonempty → Q.Nonempty → P.card + Q.card ≤ d →
      Disjoint (P.image fun u ↦ (a : ℤ) * u) (Q.image fun v ↦ c + (b : ℤ) * v) →
      ∀ D : ℤ, D ≠ 0 → ∀ S : Finset (ℕ × ℕ),
      (∀ xy ∈ S, (b : ℤ) * xy.2 = (a : ℤ) * xy.1 + c ∧
        (∀ u ∈ P, 0 < (xy.1 : ℤ) + u ∧ a * value xy.1 u ≤ N ^ K) ∧
        (∀ v ∈ Q, 0 < (xy.2 : ℤ) + v ∧ b * value xy.2 v ≤ N ^ K) ∧
        IsSquare (D * ((∏ u ∈ P, ((xy.1 : ℤ) + u)) * (∏ v ∈ Q, ((xy.2 : ℤ) + v))))) →
      (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀, hcount⟩ := PolynomialSplitKernelCount.single_square_equation K d ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN a b ha hb c P Q hP hQ hdegree hdisj D hD S hS
  have hcard : 2 ≤ (shifted a b c P Q).card := by
    rw [shifted_card ha hb c P Q hdisj]
    have hp := card_pos.mpr hP
    have hq := card_pos.mpr hQ
    omega
  have hdegree' : (shifted a b c P Q).card ≤ d := by
    rw [shifted_card ha hb c P Q hdisj]
    exact hdegree
  have hinj : Set.InjOn (fun xy : ℕ × ℕ ↦ a * xy.1) S := by
    intro xy hxy uv huv heq
    have hx : xy.1 = uv.1 := mul_left_cancel₀ (by omega : a ≠ 0) heq
    have hlineX := (hS xy hxy).1
    have hlineU := (hS uv huv).1
    rw [hx] at hlineX
    have hy : (xy.2 : ℤ) = uv.2 := mul_left_cancel₀ (by exact_mod_cast hb.ne' : (b : ℤ) ≠ 0)
      (by linarith only [hlineX, hlineU])
    exact Prod.ext hx (by exact_mod_cast hy)
  rw [← card_image_of_injOn hinj]
  apply hcount N hN (shifted a b c P Q) hcard hdegree' (D * scale a b P Q)
    (mul_ne_zero hD (scale_ne_zero ha hb P Q)) (S.image fun xy : ℕ × ℕ ↦ a * xy.1)
  intro n hn
  obtain ⟨xy, hxy, rfl⟩ := mem_image.mp hn
  refine ⟨?_, square_transfer ha hb c D P Q (hS xy hxy).1 hdisj (hS xy hxy).2.2.2⟩
  intro t ht
  rcases mem_union.mp ht with ht | ht
  · obtain ⟨u, hu, rfl⟩ := mem_image.mp ht
    constructor
    · rw [factor_left]
      exact mul_pos (by exact_mod_cast ha) ((hS xy hxy).2.1 u hu).1
    · rw [value_left]
      exact ((hS xy hxy).2.1 u hu).2
  · obtain ⟨v, hv, rfl⟩ := mem_image.mp ht
    constructor
    · rw [factor_right a b xy.1 xy.2 c v (hS xy hxy).1]
      exact mul_pos (by exact_mod_cast hb) ((hS xy hxy).2.2.1 v hv).1
    · rw [value_right a b xy.1 xy.2 c v (hS xy hxy).1]
      exact ((hS xy hxy).2.2.1 v hv).2

end PaperP1.PositiveLineSplitCount
