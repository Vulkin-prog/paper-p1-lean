module

public import PaperP1.Arithmetic.OddPivotSpecialValues
public import PaperP1.Model.AnchoredDyadicField
public import PaperP1.Model.PrivatePrimeForcing

/-! # Fair randomized orientation alone does not give a Palm law at a square anchor

The actual word is `(4,5)`, with square anchor `4`, private prime `5`
above cutoff `4`, and start `5`. It belongs to the original one-small-
pivot dyadic population. Independent fair orientation sets the only
forced source vertex correctly but hits the unsigned event only half
the time. This isolates the scope needed in the randomized argument;
it does not refute the numerical lower bound on fully private sources.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RandomOrientationSquareAnchor

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateValueSystem
  PaperP1.PrivatePrimeForcing PaperP1.UniformFubini PaperP1.OddPrimePivot

local instance randomOrientationSquareDecidable (P : Prop) : Decidable P := Classical.propDecidable P

abbrev Auxiliary := Fin 1 → F₂

theorem valueBit_square {M : ℕ} (ω : SampleSpace M) (n : ℕ) : valueBit ω (n ^ 2) = 0 := by
  simp only [valueBit, parityVec_pow_two, Finsupp.zero_apply, mul_zero, sum_const_zero]

theorem valueBit_four {M : ℕ} (ω : SampleSpace M) : valueBit ω 4 = 0 := by
  simpa only [show (2 : ℕ) ^ 2 = 4 by norm_num] using valueBit_square ω 2

theorem window_data : PaperP1.AnchoredWindowForcing.Data 8 4 2 4 (0 : Fin 2) := {
  boundary_pos := by decide
  cutoff := by decide
  small_pos := by decide
  word_width := by decide
  good := by
    intro i
    have hi : i.val.val = 1 := by
      have hne : i.val ≠ 0 := i.property
      have hv : i.val.val ≠ 0 := fun h ↦ hne (Fin.ext h)
      have hb := i.val.isLt
      omega
    rw [hi]
    norm_num only [show (4 : ℕ) + 1 = 5 by norm_num,
      PaperP1.OddPivotSpecialValues.prime (by decide : Nat.Prime 5)]
  }

theorem original_retained_membership :
    4 ∈ PaperP1.AnchoredDyadicField.retainedBoundaries 3 2 4 := by
  have hr := (PaperP1.AnchoredWindowForcing.anchor_rule_iff (j := 4) (Y := 4) (0 : Fin 2)).mpr
    window_data.good
  apply mem_filter.mpr
  refine ⟨(PaperP1.ForcingExceptionalSets.mem_boundaryBlock (by decide : 2 ≤ 3)).mpr (by decide), ?_⟩
  have hs : PaperP1.AnchoredWindowForcing.smallVertices 4 2 4 ⊆ {0} := by
    intro i hi
    exact mem_singleton.mpr (hr i (mem_filter.mp hi).2)
  exact (card_le_card hs).trans_eq (card_singleton _)

def primeFive : PrimeUpTo 8 := ⟨⟨5, by decide⟩, by decide⟩

def orientation (_u : Fin 2 → F₂) (ξ : Auxiliary) : F₂ := ξ 0

theorem auxiliary_fair : average (fun ξ : Auxiliary ↦ PaperP1.BinaryForcingFlip.bitIndicator (ξ 0)) =
    (1 / 2 : ℝ) := by
  simpa only [sub_zero] using PaperP1.BinaryForcingFlip.uniform_single_fair (0 : Fin 1) (0 : F₂)

theorem fair_for_uniform_source :
    average (fun u : Fin 2 → F₂ ↦ average (fun ξ : Auxiliary ↦
      PaperP1.BinaryForcingFlip.bitIndicator (orientation u ξ))) = (1 / 2 : ℝ) := by
  simp only [orientation, auxiliary_fair, UniformFubini.constant]

theorem singleton_basis (i : Fin 1) :
    valueSystem 8 (fun _ : Fin 1 ↦ 5) (Pi.single primeFive 1) = Pi.single i 1 := by
  apply valueSystem_prime_basis
  · change parityVec 5 5 = 1
    simp only [parityVec_apply, (by decide : Nat.Prime 5).factorization_self, Nat.cast_one]
  · intro j hji
    exact False.elim (hji (Subsingleton.elim j i))

def randomForce (ω : SampleSpace 8) (ξ : Auxiliary) : SampleSpace 8 :=
  forceWord (fun _ : Fin 1 ↦ 5) (fun _ : Fin 1 ↦ primeFive) ξ ω

theorem randomForce_value_five (ω : SampleSpace 8) (ξ : Auxiliary) :
    valueBit (randomForce ω ξ) 5 = ξ 0 := by
  have h := forceWord_hits (fun _ : Fin 1 ↦ 5) (fun _ : Fin 1 ↦ primeFive) singleton_basis ξ ω
  exact congrFun h (0 : Fin 1)

theorem only_private_prime_changes (ω : SampleSpace 8) (ξ : Auxiliary) (p : PrimeUpTo 8)
    (hp : p ≠ primeFive) : randomForce ω ξ p = ω p :=
  forceWord_preserves_nonpivot _ _ _ _ _ (fun _ ↦ hp)

theorem private_prime_above_cutoff : 4 < primeFive.val.val := by decide

theorem randomForce_matches_forced_vertex (ω : SampleSpace 8) (ξ : Auxiliary) :
    valueBit (randomForce ω ξ) 5 =
      PaperP1.UnsignedAnchoredRunForcing.startWord 1 0 (1 : Fin 2) +
        orientation (valueSystem 8 (fun i : Fin 2 ↦ 4 + i.val) ω) ξ := by
  rw [randomForce_value_five]
  simp [PaperP1.UnsignedAnchoredRunForcing.startWord, orientation]

theorem randomForce_start_iff (ω : SampleSpace 8) (ξ : Auxiliary) :
    StartEvent (valueBit (randomForce ω ξ)) 5 1 ↔ ξ 0 = 1 := by
  simp [StartEvent, valueBit_four, randomForce_value_five]

theorem forced_event_probability (ω : SampleSpace 8) :
    average (fun ξ : Auxiliary ↦ if StartEvent (valueBit (randomForce ω ξ)) 5 1 then (1 : ℝ) else 0) =
      1 / 2 := by
  have he : (fun ξ : Auxiliary ↦ if StartEvent (valueBit (randomForce ω ξ)) 5 1 then (1 : ℝ) else 0) =
      (fun ξ : Auxiliary ↦ PaperP1.BinaryForcingFlip.bitIndicator (ξ 0)) := by
    funext ξ
    by_cases hξ : ξ 0 = 1
    · rw [ite_eq_left ((randomForce_start_iff ω ξ).mpr hξ)]
      simp only [PaperP1.BinaryForcingFlip.bitIndicator, ite_eq_left hξ]
    · rw [ite_eq_right (fun h ↦ hξ ((randomForce_start_iff ω ξ).mp h))]
      simp only [PaperP1.BinaryForcingFlip.bitIndicator, ite_eq_right hξ]
  rw [he]
  exact auxiliary_fair

theorem forced_event_not_almost_sure (ω : SampleSpace 8) :
    average (fun ξ : Auxiliary ↦ if StartEvent (valueBit (randomForce ω ξ)) 5 1 then (1 : ℝ) else 0) ≠ 1 := by
  rw [forced_event_probability]
  norm_num

theorem original_event_probability :
    average (fun ω : SampleSpace 8 ↦ if StartEvent (valueBit ω) 5 1 then (1 : ℝ) else 0) =
      1 / 2 := by
  simpa only [pow_one, one_div] using
    PaperP1.UnsignedAnchoredRunForcing.start_probability window_data (by decide : 1 ≤ 1)

theorem joint_forced_event_probability :
    average (fun ω : SampleSpace 8 ↦ average (fun ξ : Auxiliary ↦
      if StartEvent (valueBit (randomForce ω ξ)) 5 1 then (1 : ℝ) else 0)) = 1 / 2 := by
  simp_rw [forced_event_probability]
  exact UniformFubini.constant _

theorem not_full_conditional_law :
    ¬∀ f : SampleSpace 8 → ℝ,
      average (fun ω : SampleSpace 8 ↦ average (fun ξ : Auxiliary ↦ f (randomForce ω ξ))) =
        average (fun ω : SampleSpace 8 ↦ if StartEvent (valueBit ω) 5 1 then f ω else 0) / (1 / 2 : ℝ) := by
  intro h
  have hc := h (fun ω ↦ if StartEvent (valueBit ω) 5 1 then (1 : ℝ) else 0)
  have he : (fun ω : SampleSpace 8 ↦ if StartEvent (valueBit ω) 5 1 then
      (if StartEvent (valueBit ω) 5 1 then (1 : ℝ) else 0) else 0) =
      (fun ω : SampleSpace 8 ↦ if StartEvent (valueBit ω) 5 1 then (1 : ℝ) else 0) := by
    funext ω
    by_cases hp : StartEvent (valueBit ω) 5 1
    · simp only [ite_eq_left hp]
    · simp only [ite_eq_right hp]
  rw [he, joint_forced_event_probability, original_event_probability] at hc
  norm_num at hc

end PaperP1.RandomOrientationSquareAnchor
