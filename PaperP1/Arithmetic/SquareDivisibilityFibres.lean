module

public import PaperP1.Analysis.ReciprocalSquareTail
public import PaperP1.Arithmetic.ShiftedDivisibilityCount

/-! # Summing actual square-divisibility fibres with their reciprocal weights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SquareDivisibilityFibres

open Finset

theorem finite_count (c₁ c₂ h : ℕ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hh : 0 < h)
    (X R : ℝ) (hX : 0 ≤ X) (hR : 0 < R)
    (S : Finset ℕ) (g : ℕ → ℕ × ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ (n : ℝ) ≤ X ∧ 0 < (g n).1 ∧ 0 < (g n).2 ∧
      c₁ * (g n).1 ^ 2 ∣ n ∧ c₂ * (g n).2 ^ 2 ∣ n + h ∧
      R ≤ (c₁ : ℝ) * ((g n).1 : ℝ) ^ 2 ∧ R ≤ (c₂ : ℝ) * ((g n).2 : ℝ) ^ 2) :
    (S.card : ℝ) ≤ 4 * X * h / R + (S.image g).card := by
  classical
  let I := S.image g
  let F := fun z : ℕ × ℕ ↦ S.filter fun n ↦ g n = z
  have hF (z : ℕ × ℕ) (hz : z ∈ I) : ((F z).card : ℝ) ≤
      X * h / ((c₁ : ℝ) * c₂ * (z.1 : ℝ) ^ 2 * (z.2 : ℝ) ^ 2) + 1 := by
    obtain ⟨n₀, hn₀, hcode⟩ := mem_image.mp hz
    have hz₁ : 0 < z.1 := hcode ▸ (hS n₀ hn₀).2.2.1
    have hz₂ : 0 < z.2 := hcode ▸ (hS n₀ hn₀).2.2.2.1
    have hb := ShiftedDivisibilityCount.uniform_finite (c₁ * z.1 ^ 2) (c₂ * z.2 ^ 2) h
      (by positivity) (by positivity) hh X hX (F z) (by
        intro n hn
        obtain ⟨hnS, hncode⟩ := mem_filter.mp hn
        have hd := hS n hnS
        exact ⟨hd.1, hd.2.1, hncode ▸ hd.2.2.2.2.1, hncode ▸ hd.2.2.2.2.2.1⟩)
    convert hb using 1
    push_cast
    ring
  have hsum : ∑ z ∈ I, 1 / ((c₁ : ℝ) * c₂ * (z.1 : ℝ) ^ 2 * (z.2 : ℝ) ^ 2) ≤ 4 / R := by
    apply ReciprocalSquareTail.weighted_product_bound (c₁ : ℝ) (c₂ : ℝ) R
      (by exact_mod_cast hc₁) (by exact_mod_cast hc₂) hR I
    intro z hz
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hz
    exact (hS n hn).2.2.2.2.2.2
  have hcard : (S.card : ℝ) = ∑ z ∈ I, ((F z).card : ℝ) := by
    have hmap : Set.MapsTo g (↑S : Set ℕ) (↑I : Set (ℕ × ℕ)) := fun _ hn ↦ mem_image_of_mem g hn
    have hh' := sum_fiberwise_of_maps_to hmap (fun _ : ℕ ↦ (1 : ℝ))
    simpa only [sum_const, nsmul_eq_mul, mul_one] using hh'.symm
  calc
    _ = ∑ z ∈ I, ((F z).card : ℝ) := hcard
    _ ≤ ∑ z ∈ I, (X * h / ((c₁ : ℝ) * c₂ * (z.1 : ℝ) ^ 2 * (z.2 : ℝ) ^ 2) + 1) := sum_le_sum hF
    _ = (X * h) * (∑ z ∈ I, 1 / ((c₁ : ℝ) * c₂ * (z.1 : ℝ) ^ 2 * (z.2 : ℝ) ^ 2)) + I.card := by
      rw [sum_add_distrib, mul_sum]
      simp only [sum_const, nsmul_eq_mul, mul_one, mul_one_div]
    _ ≤ (X * h) * (4 / R) + I.card := add_le_add
      (mul_le_mul_of_nonneg_left hsum (by positivity)) (le_refl _)
    _ = _ := by ring

end PaperP1.SquareDivisibilityFibres
