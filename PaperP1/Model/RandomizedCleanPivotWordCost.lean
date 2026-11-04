module

public import PaperP1.Model.RawAuxiliaryObservation
public import PaperP1.Model.RandomizedPrivatePalmForcing
public import PaperP1.Model.CleanPivotWordCost
public import PaperP1.Probability.RandomizedSourceFlip

/-! # Actual clean target costs for randomized private source forcing

All expectations use the original prime cylinder and the independent
auxiliary law. The local cost identity does not require orientation
fairness; that condition belongs to the separate Palm-law theorem.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RandomizedCleanPivotWordCost

open PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateValueSystem
  PaperP1.Probability PaperP1.Algebra PaperP1.UniformFubini
  PaperP1.IndependentFiniteProbability PaperP1.PrivatePivotTargetFlip

local instance randomizedCleanPivotDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {M : ℕ} {ι Ξ : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ξ]

omit [Fintype Ξ] in
theorem target_flip {A N n K : ℕ} (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (b : ι → F₂) (g : (ι → F₂) → Ξ → F₂) (ω : SampleSpace M) (ξ : Ξ) (selected : ι)
    (hwidth : K + 1 ≤ (q selected).val.val)
    (hclean : n ∈ PaperP1.CleanPivotTargets.targets A N (q selected).val.val (K + 1)
      (otherPrimes q selected)) :
    valueSystem M (fun k : Fin (K + 1) ↦ n + k.val)
        (PaperP1.RandomizedPrivatePalmForcing.force v q b g ω ξ) =
      valueSystem M (fun k : Fin (K + 1) ↦ n + k.val) ω +
        Pi.single 0 (PaperP1.RandomizedSourceFlip.flip b g selected (valueSystem M v ω, ξ)) := by
  have h := target_word_flip v q
    (PaperP1.RandomizedPrivatePalmForcing.orientedWord b (g (valueSystem M v ω) ξ))
    ω selected hwidth hclean
  simpa only [PaperP1.RandomizedPrivatePalmForcing.force, PaperP1.RandomizedPrivatePalmForcing.orientedWord,
    PaperP1.RandomizedSourceFlip.flip, PaperP1.RandomizedSourceFlip.correction_eq, valueSystem_apply] using h

theorem observation_cost {A N n K : ℕ} (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (b : ι → F₂) (g : (ι → F₂) → Ξ → F₂) (P : FiniteProbability Ξ) (selected : ι)
    (hwidth : K + 1 ≤ (q selected).val.val)
    (hclean : n ∈ PaperP1.CleanPivotTargets.targets A N (q selected).val.val (K + 1)
      (otherPrimes q selected))
    (hjoint : Function.Surjective (PaperP1.RawWordObservation.joint M v
      (fun k : Fin (K + 1) ↦ n + k.val))) (f : (Fin (K + 1) → F₂) → ℝ) :
    finiteExpectation (product (cylinderProbability M) P).weight (fun p ↦
      |f (valueSystem M (fun k : Fin (K + 1) ↦ n + k.val) p.1) -
        f (valueSystem M (fun k : Fin (K + 1) ↦ n + k.val)
          (PaperP1.RandomizedPrivatePalmForcing.force v q b g p.1 p.2))|) =
    finiteExpectation (product (uniformFiniteProbability (ι → F₂)) P).weight (fun p ↦
      average (fun z : Fin (K + 1) → F₂ ↦ |f z -
        f (if PaperP1.RandomizedSourceFlip.flip b g selected p = 1 then
          PaperP1.WordForcingFlipCost.singleFlip 0 z else z)|)) := by
  let F : (ι → F₂) → Ξ → (Fin (K + 1) → F₂) → ℝ := fun u ξ z ↦
    |f z - f (z + Pi.single 0 (PaperP1.RandomizedSourceFlip.flip b g selected (u, ξ)))|
  have ho := PaperP1.RawAuxiliaryObservation.independent_words v
    (fun k : Fin (K + 1) ↦ n + k.val) hjoint P F
  calc
    _ = finiteExpectation (product (cylinderProbability M) P).weight (fun p ↦
        F (valueSystem M v p.1) p.2 (valueSystem M (fun k : Fin (K + 1) ↦ n + k.val) p.1)) := by
      apply congrArg (finiteExpectation (product (cylinderProbability M) P).weight)
      funext p
      rw [target_flip v q b g p.1 p.2 selected hwidth hclean]
    _ = _ := ho
    _ = _ := by
      apply congrArg (finiteExpectation (product (uniformFiniteProbability (ι → F₂)) P).weight)
      funext p
      apply UniformFubini.congr
      intro z
      dsimp only [F]
      rw [PaperP1.CleanPivotWordCost.add_single_bit]

def actualUnsignedCost {K : ℕ} (v : ι → ℕ) (q : ι → PrimeUpTo M) (b : ι → F₂)
    (g : (ι → F₂) → Ξ → F₂) (P : FiniteProbability Ξ) (n : ℕ) (target : Fin (K + 1) → F₂) : ℝ :=
  finiteExpectation (product (cylinderProbability M) P).weight (fun p ↦
    |(if PaperP1.BinaryForcingFlip.orbit target
        (valueSystem M (fun k : Fin (K + 1) ↦ n + k.val) p.1) then (1 : ℝ) else 0) -
      (if PaperP1.BinaryForcingFlip.orbit target (valueSystem M (fun k : Fin (K + 1) ↦ n + k.val)
        (PaperP1.RandomizedPrivatePalmForcing.force v q b g p.1 p.2)) then 1 else 0)|)

theorem actual_cost_identity {A N n K : ℕ} (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (b : ι → F₂) (g : (ι → F₂) → Ξ → F₂) (P : FiniteProbability Ξ) (selected : ι)
    (hwidth : K + 1 ≤ (q selected).val.val)
    (hclean : n ∈ PaperP1.CleanPivotTargets.targets A N (q selected).val.val (K + 1)
      (otherPrimes q selected))
    (hjoint : Function.Surjective (PaperP1.RawWordObservation.joint M v
      (fun k : Fin (K + 1) ↦ n + k.val))) (target : Fin (K + 1) → F₂) :
    actualUnsignedCost v q b g P n target =
      PaperP1.WordForcingFlipCost.unsignedCost (product (uniformFiniteProbability (ι → F₂)) P)
        (PaperP1.RandomizedSourceFlip.flip b g selected) target 0 := by
  exact observation_cost v q b g P selected hwidth hclean hjoint
    (fun z ↦ if PaperP1.BinaryForcingFlip.orbit target z then (1 : ℝ) else 0)

theorem actual_cost_formula {A N n K : ℕ} (hK : 1 ≤ K)
    (v : ι → ℕ) (q : ι → PrimeUpTo M) (b : ι → F₂) (g : (ι → F₂) → Ξ → F₂)
    (P : FiniteProbability Ξ) (selected : ι)
    (hwidth : K + 1 ≤ (q selected).val.val)
    (hclean : n ∈ PaperP1.CleanPivotTargets.targets A N (q selected).val.val (K + 1)
      (otherPrimes q selected))
    (hjoint : Function.Surjective (PaperP1.RawWordObservation.joint M v
      (fun k : Fin (K + 1) ↦ n + k.val))) (target : Fin (K + 1) → F₂) :
    actualUnsignedCost v q b g P n target =
      2 * PaperP1.RandomizedSourceFlip.probability P b g selected * (2 ^ K : ℝ)⁻¹ := by
  rw [actual_cost_identity v q b g P selected hwidth hclean hjoint target]
  let j : Fin (K + 1) := ⟨1, by omega⟩
  have hj : j ≠ 0 := by simp [j]
  have h := PaperP1.WordForcingFlipCost.unsignedCost_eq
    (product (uniformFiniteProbability (ι → F₂)) P) (PaperP1.RandomizedSourceFlip.flip b g selected)
    target 0 j hj
  simpa only [Fintype.card_fin, Nat.add_sub_cancel, PaperP1.RandomizedSourceFlip.probability] using h

theorem actual_half_rate_lower {A N n K : ℕ} (hK : 1 ≤ K)
    (v : ι → ℕ) (q : ι → PrimeUpTo M) (b : ι → F₂) (g : (ι → F₂) → Ξ → F₂)
    (P : FiniteProbability Ξ) (selected : ι)
    (hwidth : K + 1 ≤ (q selected).val.val)
    (hclean : n ∈ PaperP1.CleanPivotTargets.targets A N (q selected).val.val (K + 1)
      (otherPrimes q selected))
    (hjoint : Function.Surjective (PaperP1.RawWordObservation.joint M v
      (fun k : Fin (K + 1) ↦ n + k.val))) (target : Fin (K + 1) → F₂)
    (hquarter : (1 / 4 : ℝ) ≤ PaperP1.RandomizedSourceFlip.probability P b g selected) :
    (2 ^ K : ℝ)⁻¹ / 2 ≤ actualUnsignedCost v q b g P n target := by
  rw [actual_cost_identity v q b g P selected hwidth hclean hjoint target]
  let j : Fin (K + 1) := ⟨1, by omega⟩
  have hj : j ≠ 0 := by simp [j]
  have h := PaperP1.WordForcingFlipCost.quarter_unsigned_cost
    (product (uniformFiniteProbability (ι → F₂)) P) (PaperP1.RandomizedSourceFlip.flip b g selected)
    target 0 j hj hquarter
  simpa only [Fintype.card_fin, Nat.add_sub_cancel] using h

end PaperP1.RandomizedCleanPivotWordCost
