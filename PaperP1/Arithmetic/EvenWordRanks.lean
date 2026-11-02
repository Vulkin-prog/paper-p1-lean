module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Tactic.FinCases
public import Lean.Elab.Tactic.Omega

/-! # The exact half-rank budget for two bounded even formal selections -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.EvenWordRanks

open Finset
open scoped symmDiff

def halfCard (E : Finset ℤ) : ℕ := E.card / 2

theorem twice_halfCard (E : Finset ℤ) (hE : Even E.card) : E.card = 2 * halfCard E := by
  obtain ⟨k, hk⟩ := hE
  unfold halfCard
  omega

theorem symmDiff_card_balance (E F : Finset ℤ) :
    (E ∆ F).card + 2 * (E ∩ F).card = E.card + F.card := by
  have h₁ := card_sdiff_add_card_inter E F
  have h₂ := card_sdiff_add_card_inter F E
  have hd : Disjoint (E \ F) (F \ E) := by
    apply disjoint_left.mpr
    intro i hi hf
    exact (mem_sdiff.mp hi).2 (mem_sdiff.mp hf).1
  have hx : (E ∆ F).card = (E \ F).card + (F \ E).card := by
    rw [Finset.symmDiff_def, card_union_of_disjoint hd]
  rw [inter_comm F E] at h₂
  omega

theorem symmDiff_even (E F : Finset ℤ) (hE : Even E.card) (hF : Even F.card) : Even (E ∆ F).card := by
  obtain ⟨a, ha⟩ := hE
  obtain ⟨b, hb⟩ := hF
  have h := symmDiff_card_balance E F
  refine ⟨(E ∆ F).card / 2, ?_⟩
  omega

theorem symmDiff_card_le (E F : Finset ℤ) : (E ∆ F).card ≤ E.card + F.card := by
  have h := symmDiff_card_balance E F
  omega

theorem symmDiff_bounded (E F : Finset ℤ) (B : ℕ)
    (hE : ∀ i ∈ E, |i| ≤ (B : ℤ)) (hF : ∀ i ∈ F, |i| ≤ (B : ℤ)) :
    ∀ i ∈ E ∆ F, |i| ≤ (B : ℤ) := by
  intro i hi
  rcases mem_symmDiff.mp hi with h | h
  · exact hE i h.1
  · exact hF i h.1

theorem card_le_radius (E : Finset ℤ) (B : ℕ) (hE : ∀ i ∈ E, |i| ≤ (B : ℤ)) :
    E.card ≤ 2 * B + 1 := by
  have hsub : E ⊆ Finset.Icc (-(B : ℤ)) B := by
    intro i hi
    have habs : -(B : ℤ) ≤ i ∧ i ≤ (B : ℤ) := abs_le.mp (hE i hi)
    exact mem_Icc.mpr habs
  calc
    _ ≤ (Finset.Icc (-(B : ℤ)) B).card := card_le_card hsub
    _ = _ := by rw [Int.card_Icc]; omega

theorem halfCard_le_radius (E : Finset ℤ) (B : ℕ) (heven : Even E.card)
    (hE : ∀ i ∈ E, |i| ≤ (B : ℤ)) : halfCard E ≤ B := by
  have hc := card_le_radius E B hE
  have he := twice_halfCard E heven
  omega

def pairRanks (E F : Finset ℤ) : Fin 3 → ℕ := ![halfCard E, halfCard F, halfCard (E ∆ F)]

theorem pairRanks_cards (E F : Finset ℤ) (hE : Even E.card) (hF : Even F.card) :
    E.card = 2 * pairRanks E F 0 ∧ F.card = 2 * pairRanks E F 1 ∧
      (E ∆ F).card = 2 * pairRanks E F 2 :=
  ⟨twice_halfCard E hE, twice_halfCard F hF, twice_halfCard (E ∆ F) (symmDiff_even E F hE hF)⟩

theorem pairRanks_bound (E F : Finset ℤ) (B q : ℕ) (hE : Even E.card) (hF : Even F.card)
    (hEB : ∀ i ∈ E, |i| ≤ (B : ℤ)) (hFB : ∀ i ∈ F, |i| ≤ (B : ℤ))
    (hEq : E.card ≤ 2 * q) (hFq : F.card ≤ 2 * q) :
    ∀ i, pairRanks E F i ≤ min (2 * q) B := by
  have hEx := twice_halfCard E hE
  have hFx := twice_halfCard F hF
  have hXEven := symmDiff_even E F hE hF
  have hXx := twice_halfCard (E ∆ F) hXEven
  have hXq := symmDiff_card_le E F
  have hEr := halfCard_le_radius E B hE hEB
  have hFr := halfCard_le_radius F B hF hFB
  have hXr := halfCard_le_radius (E ∆ F) B hXEven (symmDiff_bounded E F B hEB hFB)
  intro i
  fin_cases i
  · change halfCard E ≤ min (2 * q) B
    exact le_min (by omega) hEr
  · change halfCard F ≤ min (2 * q) B
    exact le_min (by omega) hFr
  · change halfCard (E ∆ F) ≤ min (2 * q) B
    exact le_min (by omega) hXr

end PaperP1.EvenWordRanks
