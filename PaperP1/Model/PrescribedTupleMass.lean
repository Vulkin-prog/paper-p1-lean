module

public import PaperP1.Model.WindowFamilyConditional
public import Mathlib.Data.Fin.VecNotation

/-! # Actual positive joint masses of ordered prescribed window tuples -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrescribedTupleMass

open MeasureTheory Finset PaperP1.Arithmetic PaperP1.Model.InfiniteRademacher
  PaperP1.RelativeSignIndependence PaperP1.WindowFamilyConditional

local instance prescribedTupleMassMeasurableF2 : MeasurableSpace F₂ := ⊤

abbrev append {s : ℕ} (x : Fin s → ℕ) (z : ℕ) : Fin (s + 1) → ℕ := Fin.snoc x z

def joint {s : ℕ} (L : ℕ) (c : ℕ → Fin L → F₂) (x : Fin s → ℕ) : ℝ :=
  infiniteRademacherMeasure.real {ω | sourceEvent x L (fun i ↦ c (x i)) ω}

theorem joint_nonneg {s L : ℕ} (c : ℕ → Fin L → F₂) (x : Fin s → ℕ) : 0 ≤ joint L c x :=
  measureReal_nonneg

theorem append_event {s L : ℕ} (c : ℕ → Fin L → F₂) (x : Fin s → ℕ) (z : ℕ) (ω : InfiniteSample) :
    sourceEvent (append x z) L (fun i ↦ c (append x z i)) ω ↔
      sourceEvent x L (fun i ↦ c (x i)) ω ∧ infiniteStartBits z L ω = c z := by
  simp only [sourceEvent, append, Fin.forall_fin_succ', Fin.snoc_castSucc, Fin.snoc_last]

theorem append_le {s L : ℕ} (c : ℕ → Fin L → F₂) (x : Fin s → ℕ) (z : ℕ) :
    joint L c (append x z) ≤ joint L c x := by
  exact measureReal_mono (fun ω hω ↦ ((append_event c x z ω).mp hω).1)

theorem append_eq_zero {s L : ℕ} (c : ℕ → Fin L → F₂) (x : Fin s → ℕ)
    (hx : joint L c x = 0) (z : ℕ) : joint L c (append x z) = 0 :=
  le_antisymm ((append_le c x z).trans_eq hx) (joint_nonneg c _)

theorem conditional_factor {s L : ℕ} (c : ℕ → Fin L → F₂) (x : Fin s → ℕ) (z : ℕ) :
    joint L c (append x z) = joint L c x * conditionalProbability x L (fun i ↦ c (x i)) z (c z) := by
  by_cases hx : joint L c x = 0
  · rw [hx, zero_mul, append_eq_zero c x hx z]
  have heq : {ω | sourceEvent x L (fun i ↦ c (x i)) ω ∧ infiniteStartBits z L ω = c z} =
      {ω | sourceEvent (append x z) L (fun i ↦ c (append x z i)) ω} := by
    ext ω
    exact (append_event c x z ω).symm
  unfold conditionalProbability
  rw [heq]
  change joint L c (append x z) = joint L c x * (joint L c (append x z) / joint L c x)
  field_simp

end PaperP1.PrescribedTupleMass
