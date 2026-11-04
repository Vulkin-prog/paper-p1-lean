module

public import PaperP1.Analysis.ReducedSourceMonomials

/-! # The literal source barrier after reduction has an explicit short-shift loss -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReducedSourceBarrier

open PaperP1.ReducedDyadicScales PaperP1.ReducedSourceParameter

def loss (g q : ℕ) : ℝ := 2 * (g : ℝ) ^ 2 / q

theorem loss_nonnegative (g q : ℕ) : 0 ≤ loss g q := by unfold loss; positivity

theorem quotient_barrier_identity (B D E : ℝ) (g : ℕ) (hg : 0 < g) :
    B * ((D / g) * (E / g)) ^ 2 = (B * (D * E) ^ 2) / (g : ℝ) ^ 4 := by
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  field_simp [hgR]

theorem source_barrier_lower (c₁ c₂ D E : ℝ) (g : ℕ) (hg : 0 < g)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    (c₁ * c₂ * (D * E) ^ 2) / (g : ℝ) ^ 4 ≤ c₁ * c₂ * (enlarged D g * enlarged E g) ^ 2 := by
  rw [← quotient_barrier_identity (c₁ * c₂) D E g hg]
  have hd : 0 ≤ D / g := div_nonneg hD (Nat.cast_nonneg g)
  have he : 0 ≤ E / g := div_nonneg hE (Nat.cast_nonneg g)
  have hp : (D / g) * (E / g) ≤ enlarged D g * enlarged E g :=
    mul_le_mul (raw_le_enlarged D g) (raw_le_enlarged E g) he (hd.trans (raw_le_enlarged D g))
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hd he) hp 2) (mul_nonneg hc₁ hc₂)

theorem loss_identity (B : ℝ) (g q : ℕ) (hg : 0 < g) (hq : 0 < q) :
    loss g q * (B / (g : ℝ) ^ 4) = 2 * (B / ((g ^ 2 * q : ℕ) : ℝ)) := by
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold loss
  push_cast
  field_simp [hgR, hqR]

theorem barrier_transfer (N g q : ℕ) (c₁ c₂ D E : ℝ) (hg : 0 < g) (hq : 0 < q)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hbarrier : (N : ℝ) ≤ c₁ * c₂ * (D * E) ^ 2) (heff : 1 ≤ effective N (g ^ 2 * q)) :
    (parameter N (g ^ 2 * q) : ℝ) ≤ loss g q * c₁ * c₂ * (enlarged D g * enlarged E g) ^ 2 := by
  have hsR : (0 : ℝ) < ((g ^ 2 * q : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos (pow_pos hg 2) hq
  have hd : effective N (g ^ 2 * q) ≤ (c₁ * c₂ * (D * E) ^ 2) / ((g ^ 2 * q : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right hbarrier hsR.le
  have hl := mul_le_mul_of_nonneg_left (source_barrier_lower c₁ c₂ D E g hg hc₁ hc₂ hD hE) (loss_nonnegative g q)
  rw [loss_identity (c₁ * c₂ * (D * E) ^ 2) g q hg hq] at hl
  have ht : (parameter N (g ^ 2 * q) : ℝ) ≤ loss g q * (c₁ * c₂ * (enlarged D g * enlarged E g) ^ 2) := by
    calc
      _ ≤ 2 * effective N (g ^ 2 * q) := parameter_upper N (g ^ 2 * q) heff
      _ ≤ 2 * ((c₁ * c₂ * (D * E) ^ 2) / ((g ^ 2 * q : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hd (by norm_num)
      _ ≤ _ := hl
  simpa only [mul_assoc] using ht

theorem loss_le_twice_shift (g q h : ℕ) (hq : 0 < q) (hscale : g ^ 2 * q ≤ h) : loss g q ≤ 2 * h := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hg2Nat : g ^ 2 ≤ h := (Nat.le_mul_of_pos_right _ hq).trans hscale
  have hg2 : (g : ℝ) ^ 2 ≤ h := by exact_mod_cast hg2Nat
  have hdiv : (g : ℝ) ^ 2 / q ≤ (g : ℝ) ^ 2 := by
    apply (div_le_iff₀ hqR).mpr
    have ht := mul_le_mul_of_nonneg_left hq1 (sq_nonneg (g : ℝ))
    simpa only [mul_one] using ht
  unfold loss
  calc
    _ = 2 * ((g : ℝ) ^ 2 / q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hdiv.trans hg2) (by norm_num)

end PaperP1.ReducedSourceBarrier
