module

public import PaperP1.Analysis.ShortCenteredAffineSegment

/-! # An actual short affine window covering a small parameter bucket -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AffineBucketWindow

open Set LocalAffineDerivativeFormula


theorem exists_window (r M : ℕ) (hM : 16 * (r + 1) ≤ M) (a b t₀ δ : ℝ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hleft : a + δ ≤ t₀) (hright : t₀ ≤ b - δ) :
    ∃ u c : ℝ, 0 < c ∧ c ≤ 1 ∧ c ≤ (δ / 2) / (2 * ((r + 1 : ℕ) : ℝ)) ∧
      parameter u c (1 / 2) = t₀ ∧
      (∀ v ∈ Ioo (0 : ℝ) 1, a + δ / 2 ≤ parameter u c v ∧ parameter u c v ≤ b - δ / 2) ∧
      ∀ t : ℝ, |t - t₀| ≤ δ / (M : ℝ) → ∃ v ∈ Ioo (0 : ℝ) 1, parameter u c v = t := by
  have hMpos : 0 < M := by omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hR : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ r + 1 by omega)
  have hMRbig : 16 * ((r + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMR16 : (16 : ℝ) ≤ M := by linarith only [hR, hMRbig]
  let c := 4 * δ / (M : ℝ)
  let u := t₀ - c / 2
  have hc : 0 < c := div_pos (by positivity) hMR
  have hcM : c * (M : ℝ) = 4 * δ := by
    dsimp only [c]
    field_simp
  have hcoarse : c ≤ δ / 4 := by
    have hh := mul_le_mul_of_nonneg_left hMR16 hc.le
    rw [hcM] at hh
    linarith only [hh]
  have hscale : c ≤ (δ / 2) / (2 * ((r + 1 : ℕ) : ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ((r + 1 : ℕ) : ℝ))).mpr
    have hh := mul_le_mul_of_nonneg_left hMRbig hc.le
    rw [hcM] at hh
    nlinarith only [hh]
  refine ⟨u, c, hc, by linarith only [hcoarse, hδone], hscale, ?_, ?_, ?_⟩
  · dsimp only [parameter, u]
    ring
  · intro v hv
    have hv₀ : 0 < c * v := mul_pos hc hv.1
    have hv₁ : c * v < c := by simpa only [mul_one] using mul_lt_mul_of_pos_left hv.2 hc
    dsimp only [parameter, u]
    constructor <;> linarith only [hleft, hright, hcoarse, hv₀, hv₁, hδ]
  · intro t ht
    have he : δ / (M : ℝ) = c / 4 := by dsimp only [c]; ring
    rw [he] at ht
    have hh := abs_le.mp ht
    apply image_parameter u c hc t
    constructor <;> dsimp only [u] <;> linarith only [hh.1, hh.2, hc]

end PaperP1.AffineBucketWindow
