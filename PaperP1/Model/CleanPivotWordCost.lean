module

public import PaperP1.Model.PrivatePivotTargetFlip
public import PaperP1.Model.RawWordObservation
public import PaperP1.Probability.WordForcingFlipCost

/-! # Actual single-bit arithmetic targets have exact positive word costs

The finite joint raw-value matrix is required to be surjective. This
condition is not inferred merely from clean divisibility. Together with
the proved pointwise target flip it gives an actual expectation identity
in the original prime cylinder, with the correct signed/unsigned mass.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CleanPivotWordCost

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateValueSystem PaperP1.UniformFubini
  PaperP1.PrivatePrimeForcing PaperP1.PrivatePivotTargetFlip PaperP1.AnchoredPrivateValues
  PaperP1.WordForcingFlipCost PaperP1.CleanPivotTargets

local instance cleanPivotWordCostDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

variable {M : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem add_single_bit {κ : Type*} [DecidableEq κ] (z : κ → F₂) (i : κ) (δ : F₂) :
    z + Pi.single i δ = if δ = 1 then singleFlip i z else z := by
  rcases (show δ = 0 ∨ δ = 1 by revert δ; decide) with h | h
  · subst δ
    simp
  · subst δ
    rfl

theorem observation_cost {K : ℕ} (v : ι → ℕ) (t : Fin (K + 1) → ℕ)
    (hjoint : Function.Surjective (RawWordObservation.joint M v t))
    (F : SampleSpace M → SampleSpace M) (δ : (ι → F₂) → F₂)
    (hflip : ∀ ω, valueSystem M t (F ω) = valueSystem M t ω + Pi.single 0 (δ (valueSystem M v ω)))
    (I : (Fin (K + 1) → F₂) → ℝ) :
    average (fun ω ↦ |I (valueSystem M t ω) - I (valueSystem M t (F ω))|) =
      average (fun u : ι → F₂ ↦ average (fun z : Fin (K + 1) → F₂ ↦
        |I z - I (if δ u = 1 then singleFlip 0 z else z)|)) := by
  have hp (ω : SampleSpace M) : |I (valueSystem M t ω) - I (valueSystem M t (F ω))| =
      |I (valueSystem M t ω) - I (if δ (valueSystem M v ω) = 1 then
        singleFlip 0 (valueSystem M t ω) else valueSystem M t ω)| := by
    rw [hflip, add_single_bit]
  calc
    _ = average (fun ω ↦ |I (valueSystem M t ω) -
        I (if δ (valueSystem M v ω) = 1 then singleFlip 0 (valueSystem M t ω)
          else valueSystem M t ω)|) := UniformFubini.congr hp
    _ = _ := RawWordObservation.independent_words v t hjoint
      (fun p ↦ |I p.2 - I (if δ p.1 = 1 then singleFlip 0 p.2 else p.2)|)

omit [Fintype ι] [DecidableEq ι] in
theorem sub_comm_binary (x y : F₂) : x - y = y - x := by
  revert x y
  decide

theorem signed_actual_cost {A N n K : ℕ} (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (b : ι → F₂) (selected : ι) (target : Fin (K + 1) → F₂)
    (hwidth : K + 1 ≤ (q selected).val.val)
    (hclean : n ∈ targets A N (q selected).val.val (K + 1) (otherPrimes q selected))
    (hjoint : Function.Surjective
      (RawWordObservation.joint M v (fun k : Fin (K + 1) ↦ n + k.val))) :
    average (fun ω : SampleSpace M ↦
      |(if valueSystem M (fun k : Fin (K + 1) ↦ n + k.val) ω = target then (1 : ℝ) else 0) -
        (if valueSystem M (fun k : Fin (K + 1) ↦ n + k.val) (forceWord v q b ω) = target
          then 1 else 0)|) = (2 ^ (K + 1) : ℝ)⁻¹ := by
  have hf (ω : SampleSpace M) :
      valueSystem M (fun k : Fin (K + 1) ↦ n + k.val) (forceWord v q b ω) =
      valueSystem M (fun k : Fin (K + 1) ↦ n + k.val) ω +
        Pi.single 0 ((valueSystem M v ω) selected - b selected) := by
    simpa only [valueSystem_apply, sub_comm_binary] using
      target_word_flip v q b ω selected hwidth hclean
  have h := observation_cost v (fun k : Fin (K + 1) ↦ n + k.val) hjoint
    (forceWord v q b) (fun u ↦ u selected - b selected) hf
    (fun z ↦ if z = target then (1 : ℝ) else 0)
  have hc := specified_signed_source_cost b selected target (0 : Fin (K + 1))
  simp only [Fintype.card_fin] at hc
  exact h.trans hc

theorem anchored_actual_cost {A N n K : ℕ} (v : ι → ℕ) (anchor : ι)
    (hpos : ∀ i, 0 < v i) (q : Free anchor → PrimeUpTo M) (b : ι → F₂)
    (selected : Free anchor) (target : Fin (K + 1) → F₂) (hK : 1 ≤ K)
    (hwidth : K + 1 ≤ (q selected).val.val)
    (hclean : n ∈ targets A N (q selected).val.val (K + 1) (otherPrimes q selected))
    (hjoint : Function.Surjective
      (RawWordObservation.joint M v (fun k : Fin (K + 1) ↦ n + k.val))) :
    average (fun ω : SampleSpace M ↦
      |(if BinaryForcingFlip.orbit target
          (valueSystem M (fun k : Fin (K + 1) ↦ n + k.val) ω) then (1 : ℝ) else 0) -
        (if BinaryForcingFlip.orbit target
          (valueSystem M (fun k : Fin (K + 1) ↦ n + k.val)
            (AnchoredPrivateForcing.force v anchor q b ω)) then 1 else 0)|) =
      (2 ^ K : ℝ)⁻¹ := by
  have hf := anchored_target_word_flip (A := A) (N := N) (n := n) (K := K) v anchor hpos q b
  have h := observation_cost v (fun k : Fin (K + 1) ↦ n + k.val) hjoint
    (AnchoredPrivateForcing.force v anchor q b)
    (fun u ↦ u selected.val - (b selected.val + (u anchor - b anchor)))
    (fun ω ↦ hf ω selected hwidth hclean)
    (fun z ↦ if BinaryForcingFlip.orbit target z then (1 : ℝ) else 0)
  let j : Fin (K + 1) := ⟨1, by omega⟩
  have hj : j ≠ 0 := by simp [j]
  have hc := specified_anchored_source_cost b selected.val anchor selected.property.symm target 0 j hj
  simp only [Fintype.card_fin, Nat.add_sub_cancel] at hc
  exact h.trans hc

end PaperP1.CleanPivotWordCost
