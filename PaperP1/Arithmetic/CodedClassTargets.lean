module

public import PaperP1.Arithmetic.ClassCoefficientValues
public import PaperP1.Combinatorics.BoundedSubsets
public import PaperP1.Combinatorics.RealFiniteCover
public import Mathlib.Tactic.Ring

/-! # A literal finite cover by two physical classes and their coefficients -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CodedClassTargets

open Finset PaperP1.PhysicalClassData

abbrev Record (s L : ℕ) := Finset (Option (Fin s) × Fin (L + 1)) × ℕ

def pool (s L K : ℕ) := BoundedSubsets.sets (univ : Finset (Option (Fin s) × Fin (L + 1))) K

def equations {s : ℕ} (x : Fin s → ℕ) (L H K E : ℕ) : Finset (Record s L) :=
  (pool s L K).biUnion fun C ↦ (ClassCoefficientValues.values H (sourceProduct x C) E).image (C, ·)

def Good {s L : ℕ} (C D : Finset (Option (Fin s) × Fin (L + 1))) : Prop :=
  (offsets C).Nonempty ∧ (offsets D).Nonempty ∧ Disjoint (offsets C) (offsets D)

def pairSolutions {s L : ℕ} (N : ℕ) (a b : Record s L) : Finset ℕ := by
  classical
  exact if Good a.1 b.1 then (Ico N (2 * N)).filter fun z ↦
    IsSquare ((a.2 : ℤ) * ∏ u ∈ offsets a.1, ((z : ℤ) + u)) ∧
    IsSquare ((b.2 : ℤ) * ∏ u ∈ offsets b.1, ((z : ℤ) + u)) else ∅

def targets {s : ℕ} (x : Fin s → ℕ) (L H K N E : ℕ) : Finset ℕ :=
  (equations x L H K E).biUnion fun a ↦ (equations x L H K E).biUnion (pairSolutions N a)

theorem mem_pool {s L K : ℕ} (C : Finset (Option (Fin s) × Fin (L + 1))) :
    C ∈ pool s L K ↔ C.card ≤ K := by
  simp only [pool, BoundedSubsets.mem_sets, subset_univ, true_and]

theorem card_pool (s L K : ℕ) :
    (pool s L K).card ≤ (K + 1) * ((s + 1) * (L + 1) + 1) ^ K := by
  simpa only [pool, card_univ, Fintype.card_prod, Fintype.card_option, Fintype.card_fin] using
    BoundedSubsets.card_sets (univ : Finset (Option (Fin s) × Fin (L + 1))) K

theorem mem_equations {s : ℕ} (x : Fin s → ℕ) (L H K E : ℕ) (a : Record s L) :
    a ∈ equations x L H K E ↔ a.1 ∈ pool s L K ∧
      a.2 ∈ ClassCoefficientValues.values H (sourceProduct x a.1) E := by
  simp only [equations, mem_biUnion, mem_image]
  constructor
  · rintro ⟨C, hC, d, hd, heq⟩
    subst a
    exact ⟨hC, hd⟩
  · rintro ⟨hC, hd⟩
    exact ⟨a.1, hC, a.2, hd, Prod.mk.eta⟩

theorem mem_pairSolutions {s L N z : ℕ} (a b : Record s L) :
    z ∈ pairSolutions N a b ↔ Good a.1 b.1 ∧ z ∈ Ico N (2 * N) ∧
      IsSquare ((a.2 : ℤ) * ∏ u ∈ offsets a.1, ((z : ℤ) + u)) ∧
      IsSquare ((b.2 : ℤ) * ∏ u ∈ offsets b.1, ((z : ℤ) + u)) := by
  classical
  by_cases h : Good a.1 b.1 <;> simp [pairSolutions, h, and_assoc]

theorem mem_targets {s : ℕ} (x : Fin s → ℕ) (L H K N E z : ℕ) :
    z ∈ targets x L H K N E ↔
      ∃ a ∈ equations x L H K E, ∃ b ∈ equations x L H K E, z ∈ pairSolutions N a b := by
  simp only [targets, mem_biUnion]

theorem equations_card {s : ℕ} (x : Fin s → ℕ) (L H K E : ℕ) (A : ℝ)
    (hA : ∀ C ∈ pool s L K, ((ClassCoefficientValues.values H (sourceProduct x C) E).card : ℝ) ≤ A) :
    ((equations x L H K E).card : ℝ) ≤ ((pool s L K).card : ℝ) * A := by
  apply RealFiniteCover.biUnion_card
  intro C hC
  exact (show (((ClassCoefficientValues.values H (sourceProduct x C) E).image (C, ·)).card : ℝ) ≤
    ((ClassCoefficientValues.values H (sourceProduct x C) E).card : ℝ) from by exact_mod_cast card_image_le).trans
      (hA C hC)

theorem targets_card {s : ℕ} (x : Fin s → ℕ) (L H K N E : ℕ) (A B : ℝ)
    (hBnonneg : 0 ≤ B)
    (hA : ∀ C ∈ pool s L K, ((ClassCoefficientValues.values H (sourceProduct x C) E).card : ℝ) ≤ A)
    (hB : ∀ a ∈ equations x L H K E, ∀ b ∈ equations x L H K E,
      ((pairSolutions N a b).card : ℝ) ≤ B) :
    ((targets x L H K N E).card : ℝ) ≤ (((pool s L K).card : ℝ) * A) ^ 2 * B := by
  have hE := equations_card x L H K E A hA
  calc
    _ ≤ ((equations x L H K E).card : ℝ) * (((equations x L H K E).card : ℝ) * B) := by
      apply RealFiniteCover.biUnion_card
      intro a ha
      exact RealFiniteCover.biUnion_card _ _ B (hB a ha)
    _ = ((equations x L H K E).card : ℝ) ^ 2 * B := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hE 2) hBnonneg

end PaperP1.CodedClassTargets
