module

public import PaperP1.Coding.CoordinateStep
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! # A finite potential paying for both kinds of coordinate restriction -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoordinateForms

open Finset PaperP1.Arithmetic

local instance coordinatePotentialPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {V U : Type*} [Fintype V] [DecidableEq V] [AddCommGroup U] [Module F₂ U]

local instance coordinatePotentialDecidableEq (A : Submodule F₂ U) : DecidableEq (Module.Dual F₂ A) :=
  Classical.decEq _

def originalForms (L : V → Module.Dual F₂ U) : Finset (Module.Dual F₂ U) := by
  classical
  exact (univ.image L).erase 0

def originalActive (L : V → Module.Dual F₂ U) : Finset V := by
  classical
  exact univ.filter fun v ↦ L v ≠ 0

omit [DecidableEq V] in
theorem activeCoordinates_card_le_original (L : V → Module.Dual F₂ U) (A : Submodule F₂ U) :
    (activeCoordinates L A).card ≤ (originalActive L).card := by
  classical
  apply card_le_card
  intro v hv
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  intro hz
  apply (mem_activeCoordinates L A v).mp hv
  rw [restrictForm, hz, LinearMap.zero_comp]

omit [DecidableEq V] in
theorem distinctForms_card_le_original (L : V → Module.Dual F₂ U) (A : Submodule F₂ U) :
    (distinctForms L A).card ≤ (originalForms L).card := by
  classical
  have hsub : distinctForms L A ⊆ (originalForms L).image A.dualRestrict := by
    intro α hα
    obtain ⟨hα0, v, hv⟩ := (mem_distinctForms L A α).mp hα
    have hv0 : L v ≠ 0 := by
      intro h
      have hz : restrictForm L A v = 0 := by rw [restrictForm, h, LinearMap.zero_comp]
      exact hα0 (hv.symm.trans hz)
    exact mem_image.mpr ⟨L v, mem_erase.mpr ⟨hv0, mem_image.mpr ⟨v, mem_univ _, rfl⟩⟩, hv⟩
  exact (card_le_card hsub).trans card_image_le

def potential (L : V → Module.Dual F₂ U) (K d : ℕ) (D : Finset V) : ℝ :=
  D.card + ((activeCoordinates L (zeroCoordinates L D)).card : ℝ) / (K + 1 : ℝ) +
    (((distinctForms L (zeroCoordinates L D)).card : ℝ) -
      (Module.finrank F₂ (zeroCoordinates L D) : ℝ)) / (d + 1 : ℝ)

def budget (L : V → Module.Dual F₂ U) (K d : ℕ) : ℝ :=
  ((originalActive L).card : ℝ) / (K + 1 : ℝ) +
    (((originalForms L).card : ℝ) - (Module.finrank F₂ U : ℝ)) / (d + 1 : ℝ)

omit [DecidableEq V] in
theorem budget_le_ground_card (L : V → Module.Dual F₂ U) (K d : ℕ) :
    budget L K d ≤ (Fintype.card V : ℝ) / (K + 1 : ℝ) +
      (((originalForms L).card : ℝ) - (Module.finrank F₂ U : ℝ)) / (d + 1 : ℝ) := by
  have hcard : ((originalActive L).card : ℝ) ≤ Fintype.card V := by
    exact_mod_cast card_le_univ (originalActive L)
  unfold budget
  exact add_le_add (div_le_div_of_nonneg_right hcard (by positivity)) le_rfl

omit [DecidableEq V] in
theorem potential_empty_le_budget (L : V → Module.Dual F₂ U) (K d : ℕ) :
    potential L K d ∅ ≤ budget L K d := by
  have hactive : ((activeCoordinates L (⊤ : Submodule F₂ U)).card : ℝ) ≤ (originalActive L).card := by
    exact_mod_cast activeCoordinates_card_le_original L (⊤ : Submodule F₂ U)
  have hdistinct : ((distinctForms L (⊤ : Submodule F₂ U)).card : ℝ) ≤ (originalForms L).card := by
    exact_mod_cast distinctForms_card_le_original L ⊤
  have hdenK : (0 : ℝ) ≤ K + 1 := by positivity
  have hdend : (0 : ℝ) ≤ d + 1 := by positivity
  unfold potential budget
  rw [zeroCoordinates_empty, finrank_top, card_empty, Nat.cast_zero, zero_add]
  exact add_le_add (div_le_div_of_nonneg_right hactive hdenK)
    (div_le_div_of_nonneg_right (sub_le_sub_right hdistinct _) hdend)

omit [DecidableEq V] in
theorem card_le_potential (L : V → Module.Dual F₂ U)
    (hsep : ∀ x : U, (∀ v : V, L v x = 0) → x = 0) (K d : ℕ) (D : Finset V) :
    (D.card : ℝ) ≤ potential L K d D := by
  have hdim : (Module.finrank F₂ (zeroCoordinates L D) : ℝ) ≤
      (distinctForms L (zeroCoordinates L D)).card := by
    exact_mod_cast dimension_le_distinct_card L hsep (zeroCoordinates L D)
  have ha : 0 ≤ ((activeCoordinates L (zeroCoordinates L D)).card : ℝ) / (K + 1 : ℝ) := by positivity
  have hs : 0 ≤ (((distinctForms L (zeroCoordinates L D)).card : ℝ) -
      (Module.finrank F₂ (zeroCoordinates L D) : ℝ)) / (d + 1 : ℝ) :=
    div_nonneg (sub_nonneg.mpr hdim) (by positivity)
  unfold potential
  linarith

theorem potential_step [FiniteDimensional F₂ U] (L : V → Module.Dual F₂ U)
    (K d : ℕ) (D : Finset V) (v : V)
    (hv : restrictForm L (zeroCoordinates L D) v ≠ 0)
    (hbad : K < multiplicity L (zeroCoordinates L D) (restrictForm L (zeroCoordinates L D) v) ∨
      d < (PairDecompositions.pairs (distinctForms L (zeroCoordinates L D))
        (restrictForm L (zeroCoordinates L D) v)).card) :
    potential L K d (insert v D) ≤ potential L K d D := by
  have hactive : ((activeCoordinates L (zeroCoordinates L (insert v D))).card : ℝ) +
      (multiplicity L (zeroCoordinates L D) (restrictForm L (zeroCoordinates L D) v) : ℝ) ≤
      (activeCoordinates L (zeroCoordinates L D)).card := by
    exact_mod_cast activeCoordinates_card_step L D v hv
  have hdistinct : ((distinctForms L (zeroCoordinates L (insert v D))).card : ℝ) +
      ((PairDecompositions.pairs (distinctForms L (zeroCoordinates L D))
        (restrictForm L (zeroCoordinates L D) v)).card : ℝ) + 1 ≤
      (distinctForms L (zeroCoordinates L D)).card := by
    exact_mod_cast distinctForms_card_step L D v hv
  have hdim : (Module.finrank F₂ (zeroCoordinates L (insert v D)) : ℝ) + 1 =
      Module.finrank F₂ (zeroCoordinates L D) := by exact_mod_cast step_dimension L D v hv
  have hK : (0 : ℝ) < K + 1 := by positivity
  have hd : (0 : ℝ) < d + 1 := by positivity
  have ha := div_le_div_of_nonneg_right hactive hK.le
  rw [add_div] at ha
  have hexcess : ((distinctForms L (zeroCoordinates L (insert v D))).card : ℝ) -
      Module.finrank F₂ (zeroCoordinates L (insert v D)) +
      ((PairDecompositions.pairs (distinctForms L (zeroCoordinates L D))
        (restrictForm L (zeroCoordinates L D) v)).card : ℝ) ≤
      ((distinctForms L (zeroCoordinates L D)).card : ℝ) - Module.finrank F₂ (zeroCoordinates L D) := by
    linarith
  have hs := div_le_div_of_nonneg_right hexcess hd.le
  rw [add_div] at hs
  have hpay : (1 : ℝ) ≤
      (multiplicity L (zeroCoordinates L D) (restrictForm L (zeroCoordinates L D) v) : ℝ) /
        (K + 1 : ℝ) +
      ((PairDecompositions.pairs (distinctForms L (zeroCoordinates L D))
        (restrictForm L (zeroCoordinates L D) v)).card : ℝ) / (d + 1 : ℝ) := by
    rcases hbad with hm | ht
    · have hm' : (K + 1 : ℝ) ≤
          (multiplicity L (zeroCoordinates L D) (restrictForm L (zeroCoordinates L D) v) : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hm
      have h : (1 : ℝ) ≤
          (multiplicity L (zeroCoordinates L D) (restrictForm L (zeroCoordinates L D) v) : ℝ) /
            (K + 1 : ℝ) := (le_div_iff₀ hK).mpr (by simpa only [one_mul] using hm')
      have hz : 0 ≤ ((PairDecompositions.pairs (distinctForms L (zeroCoordinates L D))
          (restrictForm L (zeroCoordinates L D) v)).card : ℝ) / (d + 1 : ℝ) := by positivity
      linarith
    · have ht' : (d + 1 : ℝ) ≤
          ((PairDecompositions.pairs (distinctForms L (zeroCoordinates L D))
            (restrictForm L (zeroCoordinates L D) v)).card : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt ht
      have h : (1 : ℝ) ≤
          ((PairDecompositions.pairs (distinctForms L (zeroCoordinates L D))
            (restrictForm L (zeroCoordinates L D) v)).card : ℝ) / (d + 1 : ℝ) :=
        (le_div_iff₀ hd).mpr (by simpa only [one_mul] using ht')
      have hz : 0 ≤ (multiplicity L (zeroCoordinates L D)
          (restrictForm L (zeroCoordinates L D) v) : ℝ) / (K + 1 : ℝ) := by positivity
      linarith
  have hvD : v ∉ D := fun h ↦ hv (restrictForm_zero_of_mem L D v h)
  unfold potential
  rw [card_insert_of_notMem hvD, Nat.cast_add, Nat.cast_one]
  linarith

end PaperP1.CoordinateForms
