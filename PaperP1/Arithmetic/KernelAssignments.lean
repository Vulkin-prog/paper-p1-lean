module

public import PaperP1.Arithmetic.ShortIntervalCongruences
public import PaperP1.Arithmetic.KernelSupportFibres

/-! # Actual window counts from assignments of distinct prime divisors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.KernelAssignments

open Finset PaperP1.ShortIntervalCongruences

def hits (P : Finset ℕ) (B U N : ℕ) : Finset ℕ :=
  (Finset.Ico U (U + N)).filter fun y ↦ ∀ p ∈ P, ∃ j : Fin B, p ∣ y - 1 + j.val

def assignmentFibre (P : Finset ℕ) (B U N : ℕ) (w : P → Fin B) : Finset ℕ :=
  fibre U N (fun p : P ↦ p.val) (fun p ↦ (w p).val)

theorem hits_subset_cover (P : Finset ℕ) (B U N : ℕ) :
    hits P B U N ⊆ (Finset.univ : Finset (P → Fin B)).biUnion (assignmentFibre P B U N) := by
  intro y hy
  obtain ⟨hy, hhit⟩ := mem_filter.mp hy
  let w : P → Fin B := fun p ↦ Classical.choose (hhit p.val p.property)
  refine mem_biUnion.mpr ⟨w, mem_univ _, mem_filter.mpr ⟨hy, ?_⟩⟩
  intro p
  exact Classical.choose_spec (hhit p.val p.property)

theorem assignment_fibre_card (P : Finset ℕ) (B U N : ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hU : 1 ≤ U) (w : P → Fin B) :
    (assignmentFibre P B U N w).card ≤ N / P.prod id + 1 := by
  have hcop : Pairwise (fun p q : P ↦ Nat.Coprime p.val q.val) := by
    intro p q hpq
    exact (Nat.coprime_primes (hP p.val p.property) (hP q.val q.property)).mpr
      (fun heq ↦ hpq (Subtype.ext heq))
  have h := card_fibre_le U N (fun p : P ↦ p.val) (fun p ↦ (w p).val) hU hcop
  have hprod : (∏ p : P, p.val) = P.prod id := Finset.prod_coe_sort P id
  rw [hprod] at h
  exact h

theorem hits_card (P : Finset ℕ) (B U N : ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hU : 1 ≤ U) :
    (hits P B U N).card ≤ B ^ P.card * (N / P.prod id + 1) := by
  calc
    _ ≤ ((Finset.univ : Finset (P → Fin B)).biUnion (assignmentFibre P B U N)).card :=
      card_le_card (hits_subset_cover P B U N)
    _ ≤ ∑ w : P → Fin B, (assignmentFibre P B U N w).card := card_biUnion_le
    _ ≤ ∑ _w : P → Fin B, (N / P.prod id + 1) :=
      sum_le_sum (fun w _ ↦ assignment_fibre_card P B U N hP hU w)
    _ = _ := by simp

/-- The `+1` is absorbed even when the squarefree modulus is larger than N. -/
theorem hits_card_real (P : Finset ℕ) (B U N : ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hU : 1 ≤ U) (hprod : P.prod id ≤ 3 * N) :
    ((hits P B U N).card : ℝ) ≤ 4 * N * (B : ℝ) ^ P.card / (P.prod id : ℕ) := by
  have hp : 0 < P.prod id := prod_pos (fun p hp ↦ (hP p hp).pos)
  have hpR : (0 : ℝ) < P.prod id := by exact_mod_cast hp
  have hdiv : ((N / P.prod id : ℕ) : ℝ) ≤ (N : ℝ) / (P.prod id : ℕ) := Nat.cast_div_le
  have hcast : ((hits P B U N).card : ℝ) ≤
      (B : ℝ) ^ P.card * (((N / P.prod id : ℕ) : ℝ) + 1) := by
    exact_mod_cast hits_card P B U N hP hU
  have hone : (1 : ℝ) ≤ 3 * N / (P.prod id : ℕ) := by
    apply (le_div_iff₀ hpR).mpr
    simpa only [one_mul, Nat.cast_mul, Nat.cast_ofNat] using (show ((P.prod id : ℕ) : ℝ) ≤ (3 * N : ℕ) by exact_mod_cast hprod)
  calc
    _ ≤ (B : ℝ) ^ P.card * (((N / P.prod id : ℕ) : ℝ) + 1) := hcast
    _ ≤ (B : ℝ) ^ P.card * (4 * N / (P.prod id : ℕ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ ≤ (N : ℝ) / (P.prod id : ℕ) + 3 * N / (P.prod id : ℕ) := add_le_add hdiv hone
        _ = _ := by ring
    _ = _ := by ring

end PaperP1.KernelAssignments
