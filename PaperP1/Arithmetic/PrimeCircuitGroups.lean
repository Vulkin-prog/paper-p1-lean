module

public import PaperP1.Arithmetic.PrimeCircuitSupports
public import PaperP1.Arithmetic.AssignedPrimeGroups

/-! # Prime groups constructed from the actual regularized relation code -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeCircuitGroups

open Finset PaperP1.Arithmetic PaperP1.PhysicalWindowRelations
  PaperP1.WindowPrimeIncidence PaperP1.PrimeCircuitSupports

local instance primeCircuitGroupsTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance primeCircuitGroupsDecEq (W : Type*) : DecidableEq W := Classical.decEq _

def activePrimes {s : ℕ} (X : Option (Fin s) → ℕ) (L : ℕ)
    (M : Submodule F₂ (code X L)) (H : ℕ) : Finset ℕ :=
  ((univ : Finset (Option (Fin s) × Fin (L + 1))).biUnion
    (fun v ↦ DefectivePredicate.oddPrimeSupport (value X L v))).filter
      fun p ↦ H < p ∧ ∃ u : Fin (L + 1),
        (none, u) ∈ occurrences X L p ∧ label X L M (none, u) ≠ 0

theorem mem_activePrimes {s : ℕ} (X : Option (Fin s) → ℕ) (L : ℕ)
    (M : Submodule F₂ (code X L)) (H p : ℕ) :
    p ∈ activePrimes X L M H ↔ H < p ∧ ∃ u : Fin (L + 1),
      (none, u) ∈ occurrences X L p ∧ label X L M (none, u) ≠ 0 := by
  refine ⟨fun h ↦ (mem_filter.mp h).2, ?_⟩
  rintro ⟨hp, u, hu, hactive⟩
  apply mem_filter.mpr
  refine ⟨mem_biUnion.mpr ⟨(none, u), mem_univ _, ?_⟩, hp, u, hu, hactive⟩
  apply LargeOddKernel.mem_oddPrimeSupport_iff_parityVec_ne_zero.mpr
  rw [(mem_occurrences X L p (none, u)).mp hu]
  exact one_ne_zero

theorem active_prime {s L H p : ℕ} {X : Option (Fin s) → ℕ}
    {M : Submodule F₂ (code X L)} (hp : p ∈ activePrimes X L M H) : Nat.Prime p := by
  obtain ⟨_, u, hu, _⟩ := (mem_activePrimes X L M H p).mp hp
  exact prime_of_mem hu

def ValidSupport {s L : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (p : ℕ)
    (F : Finset (Option (Fin s) × Fin (L + 1))) : Prop :=
  ∃ v ∈ F, v.1 = none ∧ label X L M v ≠ 0 ∧ F ∈ throughPool X L M v ∧
    (∀ w ∈ F, w ∈ occurrences X L p) ∧
    (∀ w ∈ F, w.1 = none → w = v) ∧
    (∃ w ∈ F, w.1 ≠ none) ∧ 2 ≤ F.card ∧ F.card ≤ s + 1 ∧
    (∑ w ∈ F, label X L M w) = 0

theorem exists_validSupport {s L H p : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H)
    (hp : p ∈ activePrimes X L M H) : ∃ F, ValidSupport X M p F := by
  obtain ⟨hpH, u, hu, hactive⟩ := (mem_activePrimes X L M H p).mp hp
  have hpL : L + 1 < p := hH.trans_lt hpH
  obtain ⟨D, hD, hpool, hne, hcard, _, hsum, hold⟩ :=
    old_support X M hX hpL (none, u) rfl hu hactive
  obtain ⟨hinsert, htwo, _, hzero⟩ := inserted_support X M (none, u) hu D hD hne hsum
  refine ⟨insert (none, u) D, (none, u), mem_insert_self _ _, rfl, hactive,
    mem_image.mpr ⟨D, hpool, rfl⟩, ?_, ?_, ?_, htwo, ?_, hzero⟩
  · intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · exact hu
    · exact (mem_erase.mp (hD hw)).2
  · intro w hw htarget
    rcases mem_insert.mp hw with rfl | hw
    · rfl
    · exact False.elim (hold w hw htarget)
  · obtain ⟨w, hw⟩ := hne
    exact ⟨w, mem_insert_of_mem hw, hold w hw⟩
  · omega

def support {s L : ℕ} (X : Option (Fin s) → ℕ) (M : Submodule F₂ (code X L))
    (H : ℕ) (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H) (p : ℕ) :
    Finset (Option (Fin s) × Fin (L + 1)) :=
  if hp : p ∈ activePrimes X L M H then Classical.choose (exists_validSupport X M hX hH hp)
  else ∅

theorem support_valid {s L H p : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H)
    (hp : p ∈ activePrimes X L M H) :
    ValidSupport X M p (support X M H hX hH p) := by
  simp only [support, hp, dite_eq_left]
  exact Classical.choose_spec (exists_validSupport X M hX hH hp)

abbrev groups {s L : ℕ} (X : Option (Fin s) → ℕ) (M : Submodule F₂ (code X L))
    (H : ℕ) (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H) :=
  AssignedPrimeGroups.groups (activePrimes X L M H) (support X M H hX hH)

abbrev groupValue {s L : ℕ} (X : Option (Fin s) → ℕ) (M : Submodule F₂ (code X L))
    (H : ℕ) (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H) :=
  AssignedPrimeGroups.group (activePrimes X L M H) (support X M H hX hH)

theorem group_gt_one {s L H : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H)
    {F : Finset (Option (Fin s) × Fin (L + 1))} (hF : F ∈ groups X M H hX hH) :
    1 < groupValue X M H hX hH F :=
  AssignedPrimeGroups.group_gt_one _ (fun _ hp ↦ active_prime hp) _ hF

theorem group_coprime {s L H : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H)
    {F G : Finset (Option (Fin s) × Fin (L + 1))} (hFG : F ≠ G) :
    Nat.Coprime (groupValue X M H hX hH F) (groupValue X M H hX hH G) :=
  AssignedPrimeGroups.group_coprime _ (fun _ hp ↦ active_prime hp) _ hFG

theorem group_dvd_vertex {s L H : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H)
    (F : Finset (Option (Fin s) × Fin (L + 1))) {v : Option (Fin s) × Fin (L + 1)}
    (hv : v ∈ F) : groupValue X M H hX hH F ∣ value X L v := by
  apply AssignedPrimeGroups.group_dvd _ (fun _ hp ↦ active_prime hp) _ F _
  intro p hp
  obtain ⟨hp, hsupport⟩ := (AssignedPrimeGroups.mem_primes _ _ F p).mp hp
  obtain ⟨_, _, _, _, _, hocc, _⟩ := support_valid X M hX hH hp
  apply dvd_of_mem
  exact hocc v (hsupport.symm ▸ hv)

theorem group_target_source {s L H : ℕ} (X : Option (Fin s) → ℕ)
    (M : Submodule F₂ (code X L)) (hX : ∀ i, 1 ≤ X i) (hH : L + 1 ≤ H)
    {F : Finset (Option (Fin s) × Fin (L + 1))} (hF : F ∈ groups X M H hX hH) :
    ∃ u : Fin (L + 1), (none, u) ∈ F ∧ label X L M (none, u) ≠ 0 ∧
      F ∈ throughPool X L M (none, u) ∧
      (∀ w ∈ F, w.1 = none → w = (none, u)) ∧
      ∃ a : Fin s, ∃ v : Fin (L + 1), (some a, v) ∈ F := by
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hF
  obtain ⟨⟨i, u⟩, hv, hi, hactive, hpool, _, hunique, ⟨⟨j, v⟩, hw, hj⟩, _⟩ :=
    support_valid X M hX hH hp
  change i = none at hi
  subst i
  rcases j with _ | a
  · exact False.elim (hj rfl)
  · exact ⟨u, hv, hactive, hpool, hunique, a, v, hw⟩

end PaperP1.PrimeCircuitGroups
