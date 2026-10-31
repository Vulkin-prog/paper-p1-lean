module

public import PaperP1.Coding.CoordinateRegularisation
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Rows of size at most three after zero labels have been removed -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReducedBinaryRows

open Finset PaperP1.Arithmetic PaperP1.CoordinateForms

local instance reducedRowsPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {V W : Type*} [Fintype V] [DecidableEq V] [AddCommGroup W] [Module F₂ W]

def labelSet (L : V → W) : Finset W := by
  classical
  exact (univ.image L).erase 0

def labelClass (L : V → W) (a : W) : Finset V := by
  classical
  exact univ.filter fun v ↦ L v = a

def active (L : V → W) : Finset V := by
  classical
  exact univ.filter fun v ↦ L v ≠ 0

def reduced (L : V → W) (rows : Finset (Finset V)) : Finset (Finset V) :=
  rows.image fun A ↦ A ∩ active L

def IsReducedRow (L : V → W) (A : Finset V) : Prop :=
  A.card ≤ 3 ∧ (∀ v ∈ A, L v ≠ 0) ∧ (∑ v ∈ A, L v) = 0

omit [DecidableEq V] [Module F₂ W] in
theorem mem_labelSet (L : V → W) (a : W) : a ∈ labelSet L ↔ a ≠ 0 ∧ ∃ v, L v = a := by
  classical
  simp only [labelSet, mem_erase, mem_image, mem_univ, true_and]

omit [DecidableEq V] [AddCommGroup W] [Module F₂ W] in
theorem mem_labelClass (L : V → W) (a : W) (v : V) : v ∈ labelClass L a ↔ L v = a := by
  classical
  simp only [labelClass, mem_filter, mem_univ, true_and]

omit [DecidableEq V] [Module F₂ W] in
theorem mem_active (L : V → W) (v : V) : v ∈ active L ↔ L v ≠ 0 := by
  classical
  simp only [active, mem_filter, mem_univ, true_and]

omit [Module F₂ W] in
theorem reduced_row (L : V → W) (rows : Finset (Finset V))
    (hrows : ∀ A ∈ rows, A.card ≤ 3 ∧ (∑ v ∈ A, L v) = 0) :
    ∀ A ∈ reduced L rows, IsReducedRow L A := by
  intro A hA
  obtain ⟨B, hB, rfl⟩ := mem_image.mp hA
  refine ⟨(card_le_card inter_subset_left).trans (hrows B hB).1, ?_, ?_⟩
  · intro v hv
    exact (mem_active L v).mp (mem_inter.mp hv).2
  · have hsum : (∑ v ∈ B ∩ active L, L v) = ∑ v ∈ B, L v := by
      apply sum_subset inter_subset_left
      intro v hvB hvnot
      by_contra hnonzero
      exact hvnot (mem_inter.mpr ⟨hvB, (mem_active L v).mpr hnonzero⟩)
    exact hsum.trans (hrows B hB).2

omit [Fintype V] [DecidableEq V] [Module F₂ W] in
theorem row_card_zero_two_three (L : V → W) (A : Finset V) (hA : IsReducedRow L A) :
    A.card = 0 ∨ A.card = 2 ∨ A.card = 3 := by
  have hnot : A.card ≠ 1 := by
    intro h
    obtain ⟨v, rfl⟩ := card_eq_one.mp h
    have hzero : L v = 0 := by simpa only [sum_singleton] using hA.2.2
    exact hA.2.1 v (mem_singleton_self _) hzero
  have hbound := hA.1
  omega

omit [Fintype V] in
theorem binary_labels_equal (L : V → W) (x y : V) (hxy : x ≠ y)
    (hsum : (∑ v ∈ ({x, y} : Finset V), L v) = 0) : L x = L y := by
  have h : L x + L y = 0 := by simpa only [sum_pair hxy] using hsum
  exact (eq_neg_of_add_eq_zero_left h).trans (binary_neg_eq_self _)

omit [Fintype V] in
theorem ternary_partners (L : V → W) (A : Finset V) (hA : IsReducedRow L A)
    (hcard : A.card = 3) (x : V) (hx : x ∈ A) :
    ∃ y z : V, y ≠ z ∧ x ≠ y ∧ x ≠ z ∧ A = {x, y, z} ∧
      L y ≠ 0 ∧ L z ≠ 0 ∧ L y ≠ L z ∧ L y + L z = L x := by
  have herase : (A.erase x).card = 2 := by
    have h := card_erase_add_one hx
    omega
  obtain ⟨y, z, hyz, hyzA⟩ := card_eq_two.mp herase
  have hyE : y ∈ A.erase x := by rw [hyzA]; simp
  have hzE : z ∈ A.erase x := by rw [hyzA]; simp
  have hxy : x ≠ y := (mem_erase.mp hyE).1.symm
  have hxz : x ≠ z := (mem_erase.mp hzE).1.symm
  have hshape : A = {x, y, z} := by rw [← insert_erase hx, hyzA]
  have hy0 := hA.2.1 y (mem_erase.mp hyE).2
  have hz0 := hA.2.1 z (mem_erase.mp hzE).2
  have hsum : L x + (L y + L z) = 0 := by
    have hs := hA.2.2
    rw [hshape, sum_insert (by simp [hxy, hxz]), sum_pair hyz] at hs
    exact hs
  have hpair : L y + L z = L x :=
    (eq_neg_of_add_eq_zero_right hsum).trans (binary_neg_eq_self _)
  have hlabel : L y ≠ L z := by
    intro heq
    have hdouble : L z + L z = 0 := by
      simpa only [binary_neg_eq_self] using add_neg_cancel (L z)
    have hxx : L x = 0 := by rw [← hpair, heq, hdouble]
    exact hA.2.1 x hx hxx
  exact ⟨y, z, hyz, hxy, hxz, hshape, hy0, hz0, hlabel, hpair⟩

def binaryGraph (rows : Finset (Finset V)) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ({x, y} : Finset V) ∈ rows
  symm := ⟨by
    intro x y h
    exact ⟨h.1.symm, (pair_comm x y) ▸ h.2⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

omit [Fintype V] in
theorem binary_reachable_label (L : V → W) (rows : Finset (Finset V))
    (hrows : ∀ A ∈ rows, (∑ v ∈ A, L v) = 0) {x y : V}
    (hxy : (binaryGraph rows).Reachable x y) : L x = L y := by
  obtain ⟨walk⟩ := hxy
  induction walk with
  | nil => rfl
  | cons hadj _ ih => exact (binary_labels_equal L _ _ hadj.1 (hrows _ hadj.2)).trans ih

def componentVertices (rows : Finset (Finset V)) (x : V) : Finset V := by
  classical
  exact univ.filter fun y ↦ (binaryGraph rows).Reachable x y

theorem binary_component_card_le (L : V → W) (rows : Finset (Finset V))
    (hrows : ∀ A ∈ rows, (∑ v ∈ A, L v) = 0) (K : ℕ)
    (hK : ∀ a ∈ labelSet L, (labelClass L a).card ≤ K) (x : V) (hx : L x ≠ 0) :
    (componentVertices rows x).card ≤ K := by
  classical
  have hsub : componentVertices rows x ⊆ labelClass L (L x) := by
    intro y hy
    apply (mem_labelClass L _ y).mpr
    exact (binary_reachable_label L rows hrows (mem_filter.mp hy).2).symm
  exact (card_le_card hsub).trans (hK _ ((mem_labelSet L _).mpr ⟨hx, x, rfl⟩))

end PaperP1.ReducedBinaryRows
