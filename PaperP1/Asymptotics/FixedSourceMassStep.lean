module

public import PaperP1.Model.PrescribedTupleMass
public import PaperP1.Asymptotics.FixedSourceConditionalSum
public import PaperP1.Combinatorics.TupleExtensions

/-! # One actual mass-propagation step for every fixed source family -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedSourceMassStep

open Finset PaperP1.Arithmetic PaperP1.PrescribedTupleMass PaperP1.Model.InfiniteRademacher

local instance fixedSourceMassStepMeasurableF2 : MeasurableSpace F₂ := ⊤

theorem point_step (s : ℕ) (hs : 1 ≤ s) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ Ico N (2 * N)) → ∀ c : ℕ → Fin L → F₂,
        (∑ z ∈ Ico N (2 * N), joint L c (append x z)) ≤ (N : ℝ) ^ ε * joint L c x := by
  obtain ⟨N₀, hN₀⟩ := FixedSourceConditionalSum.conditional_sum s hs C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband x hx c
  by_cases hzero : joint L c x = 0
  · simp only [append_eq_zero c x hzero, sum_const_zero, hzero, mul_zero, le_refl]
  have hpos : 0 < joint L c x := lt_of_le_of_ne (joint_nonneg c x) (Ne.symm hzero)
  have hconditional := hN₀ N hN L hband x hx (fun i ↦ c (x i)) hpos c
  calc
    _ = joint L c x * ∑ z ∈ Ico N (2 * N),
        WindowFamilyConditional.conditionalProbability x L (fun i ↦ c (x i)) z (c z) := by
      simp_rw [conditional_factor c x]
      rw [mul_sum]
    _ ≤ joint L c x * (N : ℝ) ^ ε := mul_le_mul_of_nonneg_left hconditional hpos.le
    _ = _ := mul_comm _ _

theorem family_step (s : ℕ) (hs : 1 ≤ s) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ c : ℕ → Fin L → F₂,
      ∀ F : Finset (Fin s → ℕ), (∀ x ∈ F, ∀ i, x i ∈ Ico N (2 * N)) →
        (∑ y ∈ TupleExtensions.step (Ico N (2 * N)) F, joint L c y) ≤
          (N : ℝ) ^ ε * ∑ x ∈ F, joint L c x := by
  obtain ⟨N₀, hN₀⟩ := point_step s hs C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband c F hF
  rw [TupleExtensions.step_sum, mul_sum]
  exact sum_le_sum fun x hx ↦ hN₀ N hN L hband x (hF x hx) c

theorem bounded_orders (r : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ q : ℕ, 1 ≤ q → q ≤ r →
      ∀ c : ℕ → Fin L → F₂, ∀ F : Finset (Fin q → ℕ),
        (∀ x ∈ F, ∀ i, x i ∈ Ico N (2 * N)) →
        (∑ y ∈ TupleExtensions.step (Ico N (2 * N)) F, joint L c y) ≤
          (N : ℝ) ^ ε * ∑ x ∈ F, joint L c x := by
  induction r with
  | zero => exact ⟨0, fun _ _ _ _ q hq hq0 ↦ False.elim (by omega)⟩
  | succ r ih =>
    obtain ⟨NI, hNI⟩ := ih
    obtain ⟨NS, hNS⟩ := family_step (r + 1) (by omega) C ε hε
    refine ⟨max NI NS, ?_⟩
    intro N hN L hband q hq hqr c F hF
    by_cases hqr0 : q ≤ r
    · exact hNI N (by omega) L hband q hq hqr0 c F hF
    · have heq : q = r + 1 := by omega
      subst q
      exact hNS N (by omega) L hband c F hF

end PaperP1.FixedSourceMassStep
