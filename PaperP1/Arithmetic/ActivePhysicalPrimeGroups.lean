module

public import PaperP1.Arithmetic.WindowPrimeIncidence
public import PaperP1.Arithmetic.AssignedPrimeGroups
public import PaperP1.Coding.ShortZeroSumSupportIncidence
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! # Composite prime groups on the actual active physical support after restriction

All odd primes above H are assigned by their support AFTER restriction to M.
Binary rows produced from former ternary rows are retained automatically.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActivePhysicalPrimeGroups

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.WindowPrimeIncidence PaperP1.LargeOddKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module

abbrev label (X : ι → ℕ) (L : ℕ) (M : Submodule F₂ (code X L))
    (v : ι × Fin (L + 1)) : Module.Dual F₂ M :=
  (CoordinateForms.coordinateFamily (code X L) v).comp M.subtype

def activeSupport (X : ι → ℕ) (L : ℕ) (M : Submodule F₂ (code X L)) (p : ℕ) :
    Finset (ι × Fin (L + 1)) := by
  classical
  exact (occurrences X L p).filter fun v ↦ label X L M v ≠ 0

def primePool (X : ι → ℕ) (L H : ℕ) : Finset ℕ := by
  classical
  exact ((univ : Finset (ι × Fin (L + 1))).biUnion fun v ↦
    DefectivePredicate.oddPrimeSupport (value X L v)).filter fun p ↦ H < p

def group (X : ι → ℕ) (L : ℕ) (M : Submodule F₂ (code X L)) (H : ℕ)
    (A : Finset (ι × Fin (L + 1))) : ℕ :=
  AssignedPrimeGroups.group (primePool X L H) (activeSupport X L M) A

def groups (X : ι → ℕ) (L : ℕ) (M : Submodule F₂ (code X L)) (H : ℕ) :
    Finset (Finset (ι × Fin (L + 1))) := by
  classical
  exact (AssignedPrimeGroups.groups (primePool X L H) (activeSupport X L M)).erase ∅

def largeGroups (X : ι → ℕ) (L : ℕ) (M : Submodule F₂ (code X L)) (H : ℕ) (Y : ℝ) :
    Finset (Finset (ι × Fin (L + 1))) := by
  classical
  exact (groups X L M H).filter fun A ↦ Y < (group X L M H A : ℝ)

def badPositions (X : ι → ℕ) (L : ℕ) (M : Submodule F₂ (code X L)) (H : ℕ) (Y : ℝ) :
    Finset (ι × Fin (L + 1)) := (largeGroups X L M H Y).biUnion id

omit [DecidableEq ι] in
theorem pool_prime (X : ι → ℕ) (L H p : ℕ) (hp : p ∈ primePool X L H) : Nat.Prime p := by
  classical
  obtain ⟨v, _hv, hpv⟩ := mem_biUnion.mp (mem_filter.mp hp).1
  exact prime_of_mem_oddPrimeSupport hpv

omit [DecidableEq ι] in
theorem pool_gt (X : ι → ℕ) (L H p : ℕ) (hp : p ∈ primePool X L H) : H < p :=
  (mem_filter.mp hp).2

theorem mem_groups (X : ι → ℕ) (L : ℕ) (M : Submodule F₂ (code X L)) (H : ℕ)
    (A : Finset (ι × Fin (L + 1))) :
    A ∈ groups X L M H ↔ A.Nonempty ∧ ∃ p ∈ primePool X L H, activeSupport X L M p = A := by
  classical
  simp only [groups, mem_erase, AssignedPrimeGroups.groups, mem_image, nonempty_iff_ne_empty]

omit [DecidableEq ι] in
theorem support_sum (X : ι → ℕ) (L : ℕ) (M : Submodule F₂ (code X L)) (p : ℕ) :
    (∑ v ∈ activeSupport X L M p, label X L M v) = 0 := by
  classical
  calc
    _ = ∑ v ∈ occurrences X L p, label X L M v := by
      rw [activeSupport, sum_filter]
      apply sum_congr rfl
      intro v _
      by_cases hv : label X L M v = 0 <;> simp [hv]
    _ = 0 := restricted_row_sum X L p M

theorem group_support_data (X : ι → ℕ) (L : ℕ) (M : Submodule F₂ (code X L)) (H : ℕ)
    (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H) (hι : Fintype.card ι ≤ 3)
    (A : Finset (ι × Fin (L + 1))) (hA : A ∈ groups X L M H) :
    A.Nonempty ∧ A.card ≤ 3 ∧ (∀ v ∈ A, label X L M v ≠ 0) ∧
      (∑ v ∈ A, label X L M v) = 0 := by
  classical
  obtain ⟨hAne, p, hp, rfl⟩ := (mem_groups X L M H A).mp hA
  refine ⟨hAne, ?_, fun v hv ↦ (mem_filter.mp hv).2, support_sum X L M p⟩
  exact (card_le_card (filter_subset _ _)).trans
    ((occurrences_card X L p hX (lt_of_le_of_lt hH (pool_gt X L H p hp))).trans hι)

theorem support_card (X : ι → ℕ) (L : ℕ) (M : Submodule F₂ (code X L)) (H : ℕ)
    (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H)
    (A : Finset (ι × Fin (L + 1))) (hA : A ∈ groups X L M H) : A.card ≤ Fintype.card ι := by
  classical
  obtain ⟨_hne, p, hp, rfl⟩ := (mem_groups X L M H A).mp hA
  exact (card_le_card (filter_subset _ _)).trans
    (occurrences_card X L p hX (lt_of_le_of_lt hH (pool_gt X L H p hp)))

theorem group_coprime (X : ι → ℕ) (L : ℕ) (M : Submodule F₂ (code X L)) (H : ℕ)
    (A B : Finset (ι × Fin (L + 1))) (hAB : A ≠ B) :
    (group X L M H A).Coprime (group X L M H B) :=
  AssignedPrimeGroups.group_coprime (primePool X L H) (fun p hp ↦ pool_prime X L H p hp)
    (activeSupport X L M) hAB

theorem support_at_least_two (X : ι → ℕ) (L : ℕ) (M : Submodule F₂ (code X L)) (H : ℕ)
    (A : Finset (ι × Fin (L + 1))) (hA : A ∈ groups X L M H) : 2 ≤ A.card := by
  classical
  obtain ⟨hne, p, _hp, rfl⟩ := (mem_groups X L M H A).mp hA
  by_contra h
  have hc : (activeSupport X L M p).card = 1 := by have hh := hne.card_pos; omega
  obtain ⟨v, he⟩ := card_eq_one.mp hc
  have hv : v ∈ activeSupport X L M p := by rw [he]; exact mem_singleton_self v
  have hnonzero := (mem_filter.mp hv).2
  have hsum := support_sum X L M p
  rw [he, sum_singleton] at hsum
  exact hnonzero hsum

theorem group_dvd_value (X : ι → ℕ) (L : ℕ) (M : Submodule F₂ (code X L)) (H : ℕ)
    (A : Finset (ι × Fin (L + 1))) (v : ι × Fin (L + 1)) (hv : v ∈ A) :
    group X L M H A ∣ value X L v := by
  classical
  apply AssignedPrimeGroups.group_dvd (primePool X L H) (fun p hp ↦ pool_prime X L H p hp)
    (activeSupport X L M) A (value X L v)
  intro p hp
  have he := (AssignedPrimeGroups.mem_primes _ _ _ _).mp hp |>.2
  have hvp : v ∈ activeSupport X L M p := he.symm ▸ hv
  exact dvd_of_mem (mem_filter.mp hvp).1

theorem incidence_bound (X : ι → ℕ) (L : ℕ) (M : Submodule F₂ (code X L)) (H d t : ℕ)
    (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H) (hι : Fintype.card ι ≤ d + 1)
    (hd : 1 ≤ d) (hd₂ : d ≤ 2) (ht : 2 ≤ t)
    (hno : DisjointRecoverySubspace.NoDisjointRecovery (CoordinateForms.coordinateFamily (code X L)) M d t)
    (v : ι × Fin (L + 1)) (hv : label X L M v ≠ 0) :
    ((groups X L M H).filter fun A ↦ v ∈ A).card ≤
      PhysicalLabelSupportCount.supportBound d t (t - 1) := by
  classical
  have h3 : Fintype.card ι ≤ 3 := by omega
  apply ShortZeroSumSupportIncidence.incidence_bound (CoordinateForms.coordinateFamily (code X L)) M d t hd hd₂ ht hno
    (groups X L M H)
  · intro A hA
    exact (support_card X L M H hX hH A hA).trans hι
  · intro A hA
    exact (group_support_data X L M H hX hH h3 A hA).2.2.1
  · intro A hA
    exact (group_support_data X L M H hX hH h3 A hA).2.2.2
  · exact hv

theorem kernel_le_incident_product (X : ι → ℕ) (L : ℕ) (M : Submodule F₂ (code X L)) (H : ℕ)
    (v : ι × Fin (L + 1)) (hv : label X L M v ≠ 0) :
    largeOddKernel H (value X L v) ≤
      ∏ A ∈ (groups X L M H).filter (fun A ↦ v ∈ A), group X L M H A := by
  classical
  let Q := (DefectivePredicate.oddPrimeSupport (value X L v)).filter fun p ↦ H < p
  have hocc (p : ℕ) (hp : p ∈ Q) : v ∈ occurrences X L p := by
    have hn := mem_oddPrimeSupport_iff_parityVec_ne_zero.mp (mem_filter.mp hp).1
    apply (mem_occurrences X L p v).mpr
    rcases binary_eq_zero_or_one (parityVec (value X L v) p) with hz | ho
    · exact False.elim (hn hz)
    · exact ho
  have hQP : Q ⊆ primePool X L H := by
    intro p hp
    exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨v, mem_univ _, (mem_filter.mp hp).1⟩, (mem_filter.mp hp).2⟩
  change Q.prod id ≤ _
  apply AssignedPrimeGroups.covered_prime_product_le (primePool X L H)
    (fun p hp ↦ pool_prime X L H p hp) (activeSupport X L M) Q
    ((groups X L M H).filter fun A ↦ v ∈ A) hQP
  intro p hp
  have hvp : v ∈ activeSupport X L M p := mem_filter.mpr ⟨hocc p hp, hv⟩
  exact mem_filter.mpr ⟨(mem_groups X L M H _).mpr ⟨⟨v, hvp⟩, p, hQP hp, rfl⟩, hvp⟩

theorem badPositions_card (X : ι → ℕ) (L : ℕ) (M : Submodule F₂ (code X L)) (H : ℕ) (Y : ℝ)
    (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H) (hι : Fintype.card ι ≤ 3) :
    (badPositions X L M H Y).card ≤ 3 * (largeGroups X L M H Y).card := by
  classical
  calc
    _ ≤ ∑ A ∈ largeGroups X L M H Y, A.card := card_biUnion_le
    _ ≤ ∑ _A ∈ largeGroups X L M H Y, 3 := by
      apply sum_le_sum
      intro A hA
      exact (group_support_data X L M H hX hH hι A (mem_filter.mp hA).1).2.1
    _ = _ := by simp [Nat.mul_comm]

theorem kernel_cap_away_from_bad (X : ι → ℕ) (L : ℕ) (M : Submodule F₂ (code X L)) (H d t : ℕ)
    (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H) (hι : Fintype.card ι ≤ d + 1)
    (hd : 1 ≤ d) (hd₂ : d ≤ 2) (ht : 2 ≤ t)
    (hno : DisjointRecoverySubspace.NoDisjointRecovery (CoordinateForms.coordinateFamily (code X L)) M d t)
    (Y : ℝ) (hY : 1 ≤ Y) (v : ι × Fin (L + 1)) (hv : label X L M v ≠ 0)
    (hbad : v ∉ badPositions X L M H Y) :
    (largeOddKernel H (value X L v) : ℝ) ≤ Y ^ PhysicalLabelSupportCount.supportBound d t (t - 1) := by
  classical
  let I := (groups X L M H).filter fun A ↦ v ∈ A
  have hcap (A : Finset (ι × Fin (L + 1))) (hA : A ∈ I) : (group X L M H A : ℝ) ≤ Y := by
    by_contra hh
    apply hbad
    apply mem_biUnion.mpr
    exact ⟨A, mem_filter.mpr ⟨(mem_filter.mp hA).1, lt_of_not_ge hh⟩, (mem_filter.mp hA).2⟩
  have hc := incidence_bound X L M H d t hX hH hι hd hd₂ ht hno v hv
  calc
    _ ≤ (((∏ A ∈ I, group X L M H A) : ℕ) : ℝ) := by
      exact_mod_cast kernel_le_incident_product X L M H v hv
    _ = ∏ A ∈ I, (group X L M H A : ℝ) := by rw [Nat.cast_prod]
    _ ≤ ∏ _A ∈ I, Y := Finset.prod_le_prod₀ (fun _ _ ↦ Nat.cast_nonneg _) hcap
    _ = Y ^ I.card := by rw [prod_const]
    _ ≤ _ := pow_le_pow_right₀ hY hc

end PaperP1.ActivePhysicalPrimeGroups
