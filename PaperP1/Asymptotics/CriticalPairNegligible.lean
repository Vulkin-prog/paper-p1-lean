module

public import PaperP1.Asymptotics.HalfCountSchedule
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # Uniform little-o at the actual pair scale in a critical band

The scale L*N^(-2/3) is the explicit representative of a_N asymptotic
to that scale in companion T19.14. Parameters precede every tolerance.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalPairNegligible

def scale (N L : ℕ) : ℝ := (L : ℝ) * (N : ℝ) ^ (-2 / 3 : ℝ)

def Negligible (C : ℝ) (f : ℕ → ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
    |(L : ℝ) - Real.log N / Real.log 2| ≤ C → |f N L| ≤ η * scale N L

def AtScale (C : ℝ) (a f : ℕ → ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
    |(L : ℝ) - Real.log N / Real.log 2| ≤ C → |f N L| ≤ η * a N L

theorem scale_nonneg (N L : ℕ) : 0 ≤ scale N L := by dsimp only [scale]; positivity

theorem power_small (C α η : ℝ) (hα : (2 / 3 : ℝ) < α) (hη : 0 < η) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → (N : ℝ) ^ (-α) ≤ η * scale N L := by
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption η⁻¹ (-α) (α - 2 / 3) (by linarith only [hα])
  refine ⟨10 + NG + NF, by omega, ?_⟩
  intro N hN L hband
  have hL : (1 : ℝ) ≤ L := by
    have hh := (hg N (by omega) L hband).2.2.1
    exact_mod_cast (show 1 ≤ L by omega)
  have hh : η⁻¹ * (N : ℝ) ^ (-α) ≤ (N : ℝ) ^ (-2 / 3 : ℝ) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  have hs := mul_le_mul_of_nonneg_left hh hη.le
  rw [← mul_assoc, mul_inv_cancel₀ hη.ne', one_mul] at hs
  apply hs.trans
  dsimp only [scale]
  have hl := mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (Nat.cast_nonneg N) (-2 / 3 : ℝ))
  simpa only [one_mul] using mul_le_mul_of_nonneg_left hl hη.le

theorem of_power_bound (C α : ℝ) (hα : (2 / 3 : ℝ) < α) (f : ℕ → ℕ → ℝ)
    (h : ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → |f N L| ≤ (N : ℝ) ^ (-α)) : Negligible C f := by
  obtain ⟨N₁, h⟩ := h
  intro η hη
  obtain ⟨N₂, _hN₂, hs⟩ := power_small C α η hα hη
  exact ⟨10 + N₁ + N₂, by omega, fun N hN L hband ↦
    (h N (by omega) L hband).trans (hs N (by omega) L hband)⟩

theorem of_abs_le (C K : ℝ) (hK : 0 ≤ K) (f g : ℕ → ℕ → ℝ) (hf : Negligible C f)
    (h : ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → |g N L| ≤ K * |f N L|) : Negligible C g := by
  obtain ⟨N₁, h⟩ := h
  intro η hη
  have hKp : 0 < K + 1 := by linarith only [hK]
  obtain ⟨N₂, _hN₂, hh⟩ := hf (η / (K + 1)) (div_pos hη hKp)
  refine ⟨10 + N₁ + N₂, by omega, ?_⟩
  intro N hN L hband
  have hcoef : K * (η / (K + 1)) ≤ η := by
    have he : (K + 1) * (η / (K + 1)) = η := by field_simp
    have hp : 0 ≤ η / (K + 1) := (div_pos hη hKp).le
    nlinarith only [he, hp]
  calc
    _ ≤ K * |f N L| := h N (by omega) L hband
    _ ≤ K * (η / (K + 1) * scale N L) := mul_le_mul_of_nonneg_left (hh N (by omega) L hband) hK
    _ = (K * (η / (K + 1))) * scale N L := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (scale_nonneg N L)

theorem transfer (C : ℝ) (f g : ℕ → ℕ → ℝ)
    (he : Negligible C (fun N L ↦ f N L - g N L)) (hf : Negligible C f) : Negligible C g := by
  intro η hη
  obtain ⟨N₁, _hN₁, h1⟩ := he (η / 2) (by positivity)
  obtain ⟨N₂, _hN₂, h2⟩ := hf (η / 2) (by positivity)
  refine ⟨10 + N₁ + N₂, by omega, ?_⟩
  intro N hN L hband
  have htri := abs_add_le (g N L - f N L) (f N L)
  rw [sub_add_cancel, abs_sub_comm] at htri
  linarith only [htri, h1 N (by omega) L hband, h2 N (by omega) L hband]

theorem iff_of_error (C : ℝ) (f g : ℕ → ℕ → ℝ)
    (he : Negligible C (fun N L ↦ f N L - g N L)) : Negligible C f ↔ Negligible C g := by
  refine ⟨transfer C f g he, ?_⟩
  intro hg
  have her : Negligible C (fun N L ↦ g N L - f N L) := by
    intro η hη
    obtain ⟨N₀, hN₀, h⟩ := he η hη
    exact ⟨N₀, hN₀, fun N hN L hband ↦ by simpa only [abs_sub_comm] using h N hN L hband⟩
  exact transfer C g f her hg

theorem iff_at_scale (C c d : ℝ) (hc : 0 < c) (hd : 0 < d) (a f : ℕ → ℕ → ℝ)
    (h : ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      c * scale N L ≤ a N L ∧ a N L ≤ d * scale N L) :
    Negligible C f ↔ AtScale C a f := by
  obtain ⟨N₁, h⟩ := h
  constructor
  · intro hf η hη
    obtain ⟨N₂, _hN₂, hh⟩ := hf (η * c) (mul_pos hη hc)
    refine ⟨10 + N₁ + N₂, by omega, ?_⟩
    intro N hN L hband
    have hscaled := mul_le_mul_of_nonneg_left (h N (by omega) L hband).1 hη.le
    have hsmall := hh N (by omega) L hband
    nlinarith only [hscaled, hsmall]
  · intro hf η hη
    obtain ⟨N₂, _hN₂, hh⟩ := hf (η / d) (div_pos hη hd)
    refine ⟨10 + N₁ + N₂, by omega, ?_⟩
    intro N hN L hband
    calc
      _ ≤ (η / d) * a N L := hh N (by omega) L hband
      _ ≤ (η / d) * (d * scale N L) := mul_le_mul_of_nonneg_left
        (h N (by omega) L hband).2 (div_pos hη hd).le
      _ = _ := by rw [← mul_assoc, div_mul_cancel₀ η hd.ne']

theorem transfer_at_scale (C c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (a f g : ℕ → ℕ → ℝ)
    (h : ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      c * scale N L ≤ a N L ∧ a N L ≤ d * scale N L)
    (he : Negligible C (fun N L ↦ f N L - g N L)) : AtScale C a f ↔ AtScale C a g :=
  ((iff_at_scale C c d hc hd a f h).symm.trans (iff_of_error C f g he)).trans
    (iff_at_scale C c d hc hd a g h)

end PaperP1.CriticalPairNegligible
