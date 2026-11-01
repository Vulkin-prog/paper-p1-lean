module

public import PaperP1.Arithmetic.PrimeGroupDichotomy
public import PaperP1.Arithmetic.RelativeSquarefreeParts

/-! # Residual odd primes of an actual label class lie in its incident groups -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ClassPrimeResidual

open Finset PaperP1.Arithmetic PaperP1.PhysicalWindowRelations PaperP1.PrimeCircuitSupports
  PaperP1.PrimeCircuitGroups PaperP1.PrimeGroupIncidence PaperP1.WindowPrimeIncidence
  PaperP1.RelativeSquarefreeParts PaperP1.DisjointRecoveryTheorem PaperP1.PhysicalLabelSupportCount

local instance classPrimeResidualTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance classPrimeResidualDecEq (W : Type*) : DecidableEq W := Classical.decEq _

def classProduct {s L : ℕ} (X : Option (Fin s) → ℕ) (M : Submodule F₂ (code X L))
    (α : Module.Dual F₂ M) : ℕ := ∏ v ∈ physicalClass X M α, value X L v

def oldProduct {s L : ℕ} (X : Option (Fin s) → ℕ) (M : Submodule F₂ (code X L))
    (α : Module.Dual F₂ M) : ℕ :=
  ∏ v ∈ (physicalClass X M α).filter (fun v ↦ v.1 ≠ none), value X L v

def targetPhysical {s L : ℕ} (X : Option (Fin s) → ℕ) (M : Submodule F₂ (code X L))
    (α : Module.Dual F₂ M) := (physicalClass X M α).filter fun v ↦ v.1 = none

def targetProduct {s L : ℕ} (X : Option (Fin s) → ℕ) (M : Submodule F₂ (code X L))
    (α : Module.Dual F₂ M) : ℕ := ∏ v ∈ targetPhysical X M α, value X L v

theorem classProduct_eq {s L : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (α : Module.Dual F₂ M) :
    classProduct X M α = oldProduct X M α * targetProduct X M α := by
  exact (prod_filter_mul_prod_filter_not (physicalClass X M α) (fun v ↦ v.1 = none)
    (value X L)).symm.trans (mul_comm _ _)

theorem value_pos {s L : ℕ} (X : Option (Fin s) → ℕ) (hX : ∀ i, 2 ≤ X i)
    (v : Option (Fin s) × Fin (L + 1)) : 0 < value X L v := by
  rw [value, startCompleteVertexLabel_eq_offset (show 0 < X v.1 by have h := hX v.1; omega)]
  have h := hX v.1
  omega

theorem odd_product_occurrence {s L p : ℕ} (X : Option (Fin s) → ℕ)
    (hX : ∀ i, 2 ≤ X i) (C : Finset (Option (Fin s) × Fin (L + 1)))
    (hp : p ∈ DefectivePredicate.oddPrimeSupport (∏ v ∈ C, value X L v)) :
    ∃ v ∈ C, v ∈ occurrences X L p := by
  have hne := LargeOddKernel.mem_oddPrimeSupport_iff_parityVec_ne_zero.mp hp
  rw [parityVec_prod C (value X L) (fun v _ ↦ (value_pos X hX v).ne'),
    Finsupp.finsetSum_apply] at hne
  by_contra hnot
  push Not at hnot
  apply hne
  apply sum_eq_zero
  intro v hv
  rcases binary_eq_zero_or_one (parityVec (value X L v) p) with hz | ho
  · exact hz
  · exact False.elim (hnot v hv ((mem_occurrences X L p v).mpr ho))

theorem residual_covered {s L H p : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (hX : ∀ i, 2 ≤ X i) (hH : L + 1 ≤ H)
    (hXone : ∀ i, 1 ≤ X i) {α : Module.Dual F₂ M} (hα : α ≠ 0)
    (hp : p ∈ residualSupport H (classProduct X M α) (oldProduct X M α)) :
    p ∈ activePrimes X L M H ∧
      support X M H hXone hH p ∈ incident X M H hXone hH α := by
  obtain ⟨hpodd, hpH, hpold⟩ := mem_filter.mp hp
  obtain ⟨v, hv, hvocc⟩ := odd_product_occurrence X hX (physicalClass X M α) hpodd
  have hiv : v.1 = none := by
    by_contra hi
    exact hpold ((dvd_of_mem hvocc).trans
      (dvd_prod_of_mem (value X L) (mem_filter.mpr ⟨hv, hi⟩)))
  have hlabel := (mem_physicalClass X M α v).mp hv
  have hvpair : v = (none, v.2) := Prod.ext hiv rfl
  have hpactive : p ∈ activePrimes X L M H := by
    apply (mem_activePrimes X L M H p).mpr
    refine ⟨hpH, v.2, ?_, ?_⟩
    · exact hvpair ▸ hvocc
    · rw [← hvpair, hlabel]
      exact hα
  refine ⟨hpactive, ?_⟩
  obtain ⟨w, hwF, hwtarget, _, _, hwocc, _⟩ := support_valid X M hXone hH hpactive
  have hwv : w = v := block_injective X L p hXone (hH.trans_lt hpH)
    (hwocc w hwF) hvocc (hwtarget.trans hiv.symm)
  apply mem_filter.mpr
  refine ⟨mem_image.mpr ⟨p, hpactive, rfl⟩, ?_⟩
  exact mem_image.mpr ⟨w, mem_filter.mpr ⟨hwF, hwtarget⟩, hwv ▸ hlabel⟩

theorem residual_le_incident_product {s L H : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (hX : ∀ i, 2 ≤ X i) (hH : L + 1 ≤ H)
    (hXone : ∀ i, 1 ≤ X i) {α : Module.Dual F₂ M} (hα : α ≠ 0) :
    residualPart H (classProduct X M α) (oldProduct X M α) ≤
      ∏ F ∈ incident X M H hXone hH α, groupValue X M H hXone hH F := by
  apply AssignedPrimeGroups.covered_prime_product_le _ (fun _ hp ↦ active_prime hp) _
  · intro p hp
    exact (residual_covered X M hX hH hXone hα hp).1
  · intro p hp
    exact (residual_covered X M hX hH hXone hα hp).2

theorem residual_power_bound {s L H t N k : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (hX : ∀ i, 2 ≤ X i) (hH : L + 1 ≤ H)
    (hXone : ∀ i, 1 ≤ X i) (ht : 2 ≤ t) (hN : 1 ≤ N)
    (hM : RecoveryConclusion (CoordinateForms.coordinateFamily (code X L)) M s t (t - 1))
    {α : Module.Dual F₂ M} (hα : α ≠ 0)
    (hsmall : ∀ F ∈ incident X M H hXone hH α, (groupValue X M H hXone hH F) ^ k ≤ N) :
    (residualPart H (classProduct X M α) (oldProduct X M α)) ^ k ≤
      N ^ ((t - 1) * supportBound s t (t - 1)) := by
  calc
    _ ≤ (∏ F ∈ incident X M H hXone hH α, groupValue X M H hXone hH F) ^ k :=
      Nat.pow_le_pow_left (residual_le_incident_product X M hX hH hXone hα) k
    _ = ∏ F ∈ incident X M H hXone hH α, (groupValue X M H hXone hH F) ^ k := (prod_pow _ _ _).symm
    _ ≤ ∏ _F ∈ incident X M H hXone hH α, N := prod_le_prod hsmall
    _ = N ^ (incident X M H hXone hH α).card := prod_const _
    _ ≤ _ := Nat.pow_le_pow_right hN (incident_card X M hXone hH ht hM hα)

theorem residual_real_bound {s L H t N k : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (hX : ∀ i, 2 ≤ X i) (hH : L + 1 ≤ H)
    (hXone : ∀ i, 1 ≤ X i) (ht : 2 ≤ t) (hN : 1 ≤ N) (hk : 1 ≤ k)
    (hM : RecoveryConclusion (CoordinateForms.coordinateFamily (code X L)) M s t (t - 1))
    {α : Module.Dual F₂ M} (hα : α ≠ 0)
    (hsmall : ∀ F ∈ incident X M H hXone hH α, (groupValue X M H hXone hH F) ^ k ≤ N) :
    (residualPart H (classProduct X M α) (oldProduct X M α) : ℝ) ≤
      (N : ℝ) ^ (((t - 1) * supportBound s t (t - 1) : ℕ) / (k : ℝ)) := by
  have hroot := TopProductSelection.real_root_bound hk
    (residual_power_bound X M hX hH hXone ht hN hM hα hsmall)
  have heq : ((N ^ ((t - 1) * supportBound s t (t - 1)) : ℕ) : ℝ) ^ (1 / (k : ℝ)) =
      (N : ℝ) ^ (((t - 1) * supportBound s t (t - 1) : ℕ) / (k : ℝ)) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    ring
  rwa [heq] at hroot

end PaperP1.ClassPrimeResidual
