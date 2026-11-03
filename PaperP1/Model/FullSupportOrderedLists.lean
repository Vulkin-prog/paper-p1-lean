module

public import PaperP1.Model.IndependentFullSupportTail
public import PaperP1.Combinatorics.FamilyEnumerationUpper

/-! # Actual full-support ordered lists, their exact factorial quotient, and the printed nominal weighted sum -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FullSupportOrderedLists

open Finset PaperP1.Model PaperP1.FiniteFamilyEnumeration

def atFamilies (G : Finset ℕ) (L r : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (G.powersetCard r).filter (IndependentFullSupportTail.FullSupport L)

def lists (G : Finset ℕ) (L r : ℕ) : Finset (Fin r → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin r ↦ G).filter fun n ↦
    Function.Injective n ∧ IndependentFullSupportTail.FullSupport L (tupleSet n)

def orderedMass (G : Finset ℕ) (L s : ℕ) (a : ℝ) : ℝ :=
  ∑ r ∈ Icc s G.card, a ^ r / (r.factorial : ℝ) * (lists G L r).card

def manuscriptLists (G : Finset ℕ) (L r : ℕ) : Finset (Fin r → ℕ) := by
  classical
  exact (lists G L r).filter fun n ↦
    (∀ i, Module.finrank Arithmetic.F₂ (Arithmetic.squareClassSpace (n i) L) = L) ∧
      ∀ i j, i ≠ j → L < Nat.dist (n i) (n j)

theorem manuscriptLists_subset (G : Finset ℕ) (L r : ℕ) : manuscriptLists G L r ⊆ lists G L r :=
  filter_subset _ _

theorem mem_atFamilies (G I : Finset ℕ) (L r : ℕ) :
    I ∈ atFamilies G L r ↔ I ⊆ G ∧ I.card = r ∧ IndependentFullSupportTail.FullSupport L I := by
  classical
  simp only [atFamilies, mem_filter, mem_powersetCard]
  exact and_assoc

theorem mem_lists (G : Finset ℕ) (L r : ℕ) (n : Fin r → ℕ) :
    n ∈ lists G L r ↔ (∀ i, n i ∈ G) ∧ Function.Injective n ∧
      IndependentFullSupportTail.FullSupport L (tupleSet n) := by
  classical
  simp only [lists, mem_filter, Fintype.mem_piFinset]

theorem mem_manuscriptLists (G : Finset ℕ) (L r : ℕ) (n : Fin r → ℕ) :
    n ∈ manuscriptLists G L r ↔ ((∀ i, n i ∈ G) ∧ Function.Injective n ∧
      IndependentFullSupportTail.FullSupport L (tupleSet n)) ∧
      (∀ i, Module.finrank Arithmetic.F₂ (Arithmetic.squareClassSpace (n i) L) = L) ∧
        ∀ i j, i ≠ j → L < Nat.dist (n i) (n j) := by
  classical
  simp only [manuscriptLists, mem_filter, mem_lists]

theorem card_lists (G : Finset ℕ) (L r : ℕ) :
    (lists G L r).card = (atFamilies G L r).card * r.factorial := by
  classical
  apply FamilyEnumerationUpper.factorial_count_eq _ _
    (fun I hI ↦ ((mem_atFamilies G I L r).mp hI).2.1)
  · intro n hn
    obtain ⟨hnG, hinj, hfull⟩ := (mem_lists G L r n).mp hn
    refine ⟨hinj, (mem_atFamilies G (tupleSet n) L r).mpr ⟨?_, FamilyEnumerationUpper.tupleSet_card n hinj, hfull⟩⟩
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_image.mp hx
    exact hnG i
  · intro I hI n hinj hset
    obtain ⟨hIG, _hcard, hfull⟩ := (mem_atFamilies G I L r).mp hI
    apply (mem_lists G L r n).mpr
    refine ⟨?_, hinj, hset.symm ▸ hfull⟩
    intro i
    apply hIG
    rw [← hset]
    exact mem_image.mpr ⟨i, mem_univ _, rfl⟩

theorem layer_weight (G : Finset ℕ) (L r : ℕ) (a : ℝ) :
    a ^ r / (r.factorial : ℝ) * (lists G L r).card = (atFamilies G L r).card * a ^ r := by
  rw [card_lists, Nat.cast_mul]
  have hf : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  field_simp

theorem ordered_mass_eq (G : Finset ℕ) (L s : ℕ) (a : ℝ) :
    orderedMass G L s a = ∑ I ∈ IndependentFullSupportTail.families G L s, a ^ I.card := by
  classical
  let F := IndependentFullSupportTail.families G L s
  have hsplit := sum_fiberwise_of_maps_to (s := F) (t := Icc s G.card)
    (g := fun I : Finset ℕ ↦ I.card) (by
      intro I hI
      obtain ⟨hIG, hsize, _hfull⟩ := (IndependentFullSupportTail.mem_families G I L s).mp hI
      exact mem_Icc.mpr ⟨hsize, card_le_card hIG⟩) (fun I ↦ a ^ I.card)
  calc
    _ = ∑ r ∈ Icc s G.card, (atFamilies G L r).card * a ^ r :=
      sum_congr rfl (fun r _ ↦ layer_weight G L r a)
    _ = ∑ r ∈ Icc s G.card, ∑ I ∈ F.filter (fun I ↦ I.card = r), a ^ I.card := by
      apply sum_congr rfl
      intro r hr
      have hfilter : F.filter (fun I ↦ I.card = r) = atFamilies G L r := by
        ext I
        rw [mem_filter, IndependentFullSupportTail.mem_families, mem_atFamilies]
        constructor
        · rintro ⟨⟨hIG, _hsize, hfull⟩, hcard⟩
          exact ⟨hIG, hcard, hfull⟩
        · rintro ⟨hIG, hcard, hfull⟩
          exact ⟨⟨hIG, by have h := (mem_Icc.mp hr).1; omega, hfull⟩, hcard⟩
      rw [hfilter]
      calc
        _ = ∑ _I ∈ atFamilies G L r, a ^ r := by simp
        _ = _ := sum_congr rfl (fun I hI ↦ by rw [((mem_atFamilies G I L r).mp hI).2.1])
    _ = _ := hsplit

theorem nominal_weight_formula (G : Finset ℕ) (L s : ℕ) (u : ℝ) :
    orderedMass G L s (u * (2 ^ L : ℝ)⁻¹) =
      ∑ r ∈ Icc s G.card, (u ^ r / (r.factorial : ℝ)) * ((lists G L r).card * ((2 ^ L : ℝ)⁻¹) ^ r) := by
  apply sum_congr rfl
  intro r _
  rw [mul_pow]
  ring

end PaperP1.FullSupportOrderedLists
