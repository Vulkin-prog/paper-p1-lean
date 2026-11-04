module

public import PaperP1.Combinatorics.SingletonExtensionWeights
public import PaperP1.Combinatorics.TwoEdgeTripleCover
public import Mathlib.Tactic.Linarith

/-! # Actual triple mass and designated-pair mass, with an explicit overcount

A designated pair with a nonexceptional target has a unique source. The
entire overcount is therefore bounded by the actual exceptional target
mass, without discarding triples which contain two or three source pairs.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairGeneratedTripleWeights

open Finset

variable {ι : Type*} [DecidableEq ι]

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def points (G : Finset ι) (E : Finset (Finset ι)) : Finset (Finset ι × ι) :=
  (E ×ˢ G).filter fun p ↦ p.2 ∉ p.1

def families (G : Finset ι) (E : Finset (Finset ι)) : Finset (Finset ι) :=
  (points G E).image SingletonExtensionWeights.join

def designated (G : Finset ι) (E : Finset (Finset ι)) (q : Finset ι → ℝ) : ℝ :=
  ∑ p ∈ points G E, q (SingletonExtensionWeights.join p)

def mass (G : Finset ι) (E : Finset (Finset ι)) (q : Finset ι → ℝ) : ℝ :=
  ∑ I ∈ families G E, q I

def exceptional (G : Finset ι) (E : Finset (Finset ι)) (bad : Finset ι → Finset ι)
    (q : Finset ι → ℝ) : ℝ :=
  ∑ p ∈ (points G E).filter (fun p ↦ p.2 ∈ bad p.1), q (SingletonExtensionWeights.join p)

theorem point_data {G : Finset ι} {E : Finset (Finset ι)} {p : Finset ι × ι}
    (hp : p ∈ points G E) : p.1 ∈ E ∧ p.2 ∈ G ∧ p.2 ∉ p.1 := by
  obtain ⟨hbox, hfresh⟩ := mem_filter.mp hp
  obtain ⟨he, hz⟩ := mem_product.mp hbox
  exact ⟨he, hz, hfresh⟩

theorem family_data {G : Finset ι} {E : Finset (Finset ι)}
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) {I : Finset ι} (hI : I ∈ families G E) :
    I ⊆ G ∧ I.card = 3 ∧ ∃ e ∈ E, e ⊆ I := by
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hI
  obtain ⟨he, hz, hfresh⟩ := point_data hp
  have hjoin : SingletonExtensionWeights.join p = insert p.2 p.1 := union_singleton _ _
  rw [hjoin]
  exact ⟨insert_subset_iff.mpr ⟨hz, (hE p.1 he).1⟩,
    by rw [card_insert_of_notMem hfresh, (hE p.1 he).2], p.1, he, subset_insert _ _⟩

theorem families_eq {G : Finset ι} {E : Finset (Finset ι)}
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) :
    families G E = (G.powersetCard 3).filter fun I ↦ ∃ e ∈ E, e ⊆ I := by
  ext I
  constructor
  · intro hI
    obtain ⟨hIG, hcard, he⟩ := family_data hE hI
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hIG, hcard⟩, he⟩
  · intro hI
    obtain ⟨hIG, hcard⟩ := mem_powersetCard.mp (mem_filter.mp hI).1
    obtain ⟨e, he, heI⟩ := (mem_filter.mp hI).2
    obtain ⟨z, hzI, hze, hjoin⟩ := TwoEdgeTripleCover.third_vertex hcard (hE e he).2 heI
    exact mem_image.mpr ⟨(e, z), mem_filter.mpr ⟨mem_product.mpr ⟨he, hIG hzI⟩, hze⟩, hjoin.symm⟩

theorem designated_iterated (G : Finset ι) (E : Finset (Finset ι)) (q : Finset ι → ℝ) :
    designated G E q = ∑ e ∈ E, ∑ z ∈ G \ e, q (insert z e) := by
  simp only [designated, points, sum_filter, sum_product, sdiff_eq_filter,
    SingletonExtensionWeights.join, union_singleton]

theorem retained_injective (G : Finset ι) (E : Finset (Finset ι)) (bad : Finset ι → Finset ι)
    (hunique : ∀ p ∈ points G E, p.2 ∉ bad p.1 →
      ∀ f ∈ E, f ⊆ SingletonExtensionWeights.join p → f = p.1) :
    Set.InjOn (SingletonExtensionWeights.join (ι := ι))
      (((points G E).filter fun p ↦ p.2 ∉ bad p.1) : Set (Finset ι × ι)) := by
  intro p hp q hq hjoin
  obtain ⟨hpP, hpBad⟩ := mem_filter.mp hp
  obtain ⟨hqP, _hqBad⟩ := mem_filter.mp hq
  have hqE := (point_data hqP).1
  have hqp : q.1 ⊆ SingletonExtensionWeights.join p := by
    rw [hjoin]
    exact subset_union_left
  have heq : q.1 = p.1 := hunique p hpP hpBad q.1 hqE hqp
  have hz : p.2 ∈ SingletonExtensionWeights.join q := by rw [← hjoin]; simp [SingletonExtensionWeights.join]
  have hzeq : p.2 = q.2 := by
    rcases mem_union.mp hz with hz | hz
    · exact False.elim ((point_data hpP).2.2 (heq ▸ hz))
    · exact mem_singleton.mp hz
  exact Prod.ext heq.symm hzeq

theorem finite_error (G : Finset ι) (E : Finset (Finset ι)) (bad : Finset ι → Finset ι)
    (q : Finset ι → ℝ) (hq : ∀ I, 0 ≤ q I)
    (hunique : ∀ p ∈ points G E, p.2 ∉ bad p.1 →
      ∀ f ∈ E, f ⊆ SingletonExtensionWeights.join p → f = p.1) :
    |mass G E q - designated G E q| ≤ exceptional G E bad q := by
  have hup : mass G E q ≤ designated G E q := sum_image_le_of_nonneg (fun I _ ↦ hq I)
  let P := (points G E).filter fun p ↦ p.2 ∉ bad p.1
  have hlow : (∑ p ∈ P, q (SingletonExtensionWeights.join p)) ≤ mass G E q := by
    rw [← sum_image (retained_injective G E bad hunique)]
    exact sum_le_sum_of_subset_of_nonneg (image_subset_image (filter_subset _ _)) (fun I _ _ ↦ hq I)
  have hsplit := sum_filter_add_sum_filter_not (points G E) (fun p ↦ p.2 ∈ bad p.1)
    (fun p ↦ q (SingletonExtensionWeights.join p))
  rw [abs_of_nonpos (sub_nonpos.mpr hup)]
  change _ ≤ exceptional G E bad q
  change exceptional G E bad q + (∑ p ∈ P, q (SingletonExtensionWeights.join p)) = designated G E q at hsplit
  linarith only [hlow, hsplit]

end PaperP1.PairGeneratedTripleWeights
