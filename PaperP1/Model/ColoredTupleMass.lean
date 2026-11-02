module

public import PaperP1.Model.ColoredWindowConditional
public import PaperP1.Model.ColoredReplicaMass
public import Mathlib.Data.Fin.VecNotation

/-! # Actual colored ordered-tuple masses and their exact conditional factorization -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ColoredTupleMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.ColoredPrimeSamples
  PaperP1.UniformFubini

local instance coloredTupleMassTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance coloredTupleMassDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {κ : Type*} [Fintype κ]

abbrev append {s : ℕ} (x : Fin s → ℕ) (z : ℕ) : Fin (s + 1) → ℕ := Fin.snoc x z

def event {q M L : ℕ} (Y : ℕ) (χ : ℕ → κ) (c : ℕ → ℕ → Fin L → F₂)
    (x : Fin q → ℕ) (ω : Sample κ M) : Prop :=
  ∀ i, start M Y (x i) L (χ i.val) ω = c i.val (x i)

def joint {q : ℕ} (M Y L : ℕ) (χ : ℕ → κ) (c : ℕ → ℕ → Fin L → F₂) (x : Fin q → ℕ) : ℝ :=
  average (fun ω : Sample κ M ↦ if event Y χ c x ω then 1 else 0)

def colors (q : ℕ) (χ : ℕ → κ) : Option (Fin q) → κ :=
  fun i ↦ match i with
    | none => χ q
    | some j => χ j.val

def conditional {q : ℕ} (M Y L : ℕ) (χ : ℕ → κ) (c : ℕ → ℕ → Fin L → F₂)
    (x : Fin q → ℕ) (z : ℕ) : ℝ :=
  ColoredWindowConditional.conditionalProbability M Y L x z (colors q χ) (fun i ↦ c i.val (x i)) (c q z)

theorem joint_nonneg {q : ℕ} (M Y L : ℕ) (χ : ℕ → κ) (c : ℕ → ℕ → Fin L → F₂) (x : Fin q → ℕ) :
    0 ≤ joint M Y L χ c x := by
  apply UniformFubini.nonneg
  intro ω
  split_ifs <;> norm_num

omit [Fintype κ] in
theorem append_event {q M L : ℕ} (Y : ℕ) (χ : ℕ → κ) (c : ℕ → ℕ → Fin L → F₂)
    (x : Fin q → ℕ) (z : ℕ) (ω : Sample κ M) :
    event Y χ c (append x z) ω ↔ event Y χ c x ω ∧ start M Y z L (χ q) ω = c q z := by
  simp only [event, append, Fin.forall_fin_succ', Fin.snoc_castSucc, Fin.snoc_last,
    Fin.val_castSucc, Fin.val_last]

theorem append_le {q : ℕ} (M Y L : ℕ) (χ : ℕ → κ) (c : ℕ → ℕ → Fin L → F₂)
    (x : Fin q → ℕ) (z : ℕ) : joint M Y L χ c (append x z) ≤ joint M Y L χ c x := by
  unfold joint average PaperP1.Algebra.finiteExpectation
  apply sum_le_sum
  intro ω _
  apply mul_le_mul_of_nonneg_left _ ((PaperP1.Probability.uniformFiniteProbability (Sample κ M)).weight_nonneg ω)
  by_cases hx : event Y χ c x ω
  · simp only [hx, ite_true]
    split_ifs <;> norm_num
  · have hz : ¬event Y χ c (append x z) ω := fun h ↦ hx ((append_event Y χ c x z ω).mp h).1
    simp only [hx, hz, ite_false, le_refl]

theorem append_eq_zero {q : ℕ} (M Y L : ℕ) (χ : ℕ → κ) (c : ℕ → ℕ → Fin L → F₂)
    (x : Fin q → ℕ) (hx : joint M Y L χ c x = 0) (z : ℕ) : joint M Y L χ c (append x z) = 0 :=
  le_antisymm ((append_le M Y L χ c x z).trans_eq hx) (joint_nonneg M Y L χ c _)

theorem source_mass_eq {q : ℕ} (M Y L : ℕ) (χ : ℕ → κ) (c : ℕ → ℕ → Fin L → F₂)
    (x : Fin q → ℕ) (z : ℕ) :
    CompatibleSourcePrescriptions.sourceMass (ColoredWindowConditional.systems M Y L x z (colors q χ))
      (fun i ↦ c i.val (x i)) = joint M Y L χ c x := by
  unfold CompatibleSourcePrescriptions.sourceMass joint
  apply UniformFubini.congr
  intro ω
  by_cases h : event Y χ c x ω <;> simp only [event, ColoredWindowConditional.systems, colors] at h ⊢ <;>
    simp only [h, ite_false]

theorem conditional_ratio {q : ℕ} (M Y L : ℕ) (χ : ℕ → κ) (c : ℕ → ℕ → Fin L → F₂)
    (x : Fin q → ℕ) (z : ℕ) :
    conditional M Y L χ c x z = joint M Y L χ c (append x z) / joint M Y L χ c x := by
  unfold conditional ColoredWindowConditional.conditionalProbability CompatibleSourcePrescriptions.conditionalProbability
  rw [source_mass_eq]
  congr 1
  unfold joint
  apply UniformFubini.congr
  intro ω
  simp only [ColoredWindowConditional.systems, colors, append_event]
  by_cases h : event Y χ c x ω ∧ start M Y z L (χ q) ω = c q z <;>
    simp only [event] at h ⊢ <;> simp only [h, ite_false]

theorem conditional_factor {q : ℕ} (M Y L : ℕ) (χ : ℕ → κ) (c : ℕ → ℕ → Fin L → F₂)
    (x : Fin q → ℕ) (z : ℕ) :
    joint M Y L χ c (append x z) = joint M Y L χ c x * conditional M Y L χ c x z := by
  rw [conditional_ratio]
  by_cases hx : joint M Y L χ c x = 0
  · rw [hx, zero_mul, append_eq_zero M Y L χ c x hx z]
  · field_simp

end PaperP1.ColoredTupleMass
