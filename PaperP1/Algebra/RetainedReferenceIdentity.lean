module

public import PaperP1.Combinatorics.RetainedFamilyEnumeration
public import Mathlib.Tactic.Ring.Basic

/-! # Exact heterogeneous retained-reference identity and its two independent deficits -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedReferenceIdentity

open Finset PaperP1.Affine PaperP1.RetainedDependence PaperP1.RetainedFamilyEnumeration PaperP1.Algebra

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {U κ R : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq κ] [CommRing R]
variable (S : κ → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

def familyTerm (p : κ → R) (t : R) (I : Finset κ) : R := (∏ x ∈ I, p x) * t ^ I.card

def independentReference (G : Finset κ) (p : κ → R) (t : R) : R := ∏ x ∈ G, (1 + p x * t)

def pairReference (G : Finset κ) (E : Finset (Finset κ)) (p : κ → R) (q : Finset κ → R) (t : R) : R :=
  ∑ e ∈ E, q e * t ^ 2 * independentReference (G \ e) p t

def directDeficit (G : Finset κ) (p : κ → R) (t : R) : R := by
  classical
  exact ∑ I ∈ G.powerset.filter (fun I ↦ relativeNullityOn S I ≠ 0), familyTerm p t I

def failedExtensions (G e : Finset κ) : Finset (Finset κ) := by
  classical
  exact (G \ e).powerset.filter (fun A ↦ ¬ Compressed S e (e ∪ A))

def compressedDeficit (G : Finset κ) (E : Finset (Finset κ))
    (p : κ → R) (q : Finset κ → R) (t : R) : R :=
  ∑ e ∈ E, ∑ A ∈ failedExtensions S G e, q e * t ^ 2 * familyTerm p t A

def retainedValue (G : Finset κ) (E : Finset (Finset κ)) (q : Finset κ → R) (t : R) : R :=
  ∑ I ∈ retainedSets G (Retained S E), q I * t ^ I.card

omit [DecidableEq κ] in
theorem independentReference_expansion (G : Finset κ) (p : κ → R) (t : R) :
    independentReference G p t = ∑ I ∈ G.powerset, familyTerm p t I := by
  classical
  unfold independentReference
  rw [prod_one_add]
  apply sum_congr rfl
  intro I _hI
  simp only [familyTerm, prod_mul_distrib, prod_const]

omit [∀ i, Fintype (S i)] [DecidableEq κ] in
theorem direct_plus_deficit (G : Finset κ) (p : κ → R) (t : R) :
    (∑ I ∈ directFamilies S G, familyTerm p t I) + directDeficit S G p t = independentReference G p t := by
  classical
  unfold directFamilies directDeficit
  rw [sum_filter_add_sum_filter_not, independentReference_expansion]

omit [∀ i, Fintype (S i)] in
theorem extensions_plus_failed (G e : Finset κ) (p : κ → R) (q : Finset κ → R) (t : R) :
    (∑ A ∈ extensions S G e, q e * t ^ 2 * familyTerm p t A) +
      (∑ A ∈ failedExtensions S G e, q e * t ^ 2 * familyTerm p t A) =
        q e * t ^ 2 * independentReference (G \ e) p t := by
  classical
  unfold extensions failedExtensions
  rw [sum_filter_add_sum_filter_not, independentReference_expansion, mul_sum]

theorem retained_decomposition (G : Finset κ) (E : Finset (Finset κ))
    (hcard : ∀ e ∈ E, e.card = 2) (hpos : ∀ e ∈ E, 0 < relativeNullityOn S e)
    (hground : ∀ e ∈ E, e ⊆ G) (p : κ → R) (q : Finset κ → R) (t : R)
    (hdirect : ∀ I ∈ directFamilies S G, q I = ∏ x ∈ I, p x)
    (hcompressed : ∀ e ∈ E, ∀ A ∈ extensions S G e, q (e ∪ A) = q e * ∏ x ∈ A, p x) :
    retainedValue S G E q t = (∑ I ∈ directFamilies S G, familyTerm p t I) +
      ∑ e ∈ E, ∑ A ∈ extensions S G e, q e * t ^ 2 * familyTerm p t A := by
  classical
  unfold retainedValue
  rw [retained_sum_decomposition S G E hcard hpos hground]
  congr 1
  · apply sum_congr rfl
    intro I hI
    rw [hdirect I hI]
    rfl
  · apply sum_congr rfl
    intro e he
    apply sum_congr rfl
    intro A hA
    have hdis := extension_disjoint G e A (mem_powerset.mp (mem_filter.mp hA).1)
    have hcardUnion : (e ∪ A).card = A.card + 2 := by
      rw [card_union_of_disjoint hdis, hcard e he]
      omega
    rw [hcompressed e he A hA, hcardUnion, pow_add]
    unfold familyTerm
    ring1

theorem retained_identity (G : Finset κ) (E : Finset (Finset κ))
    (hcard : ∀ e ∈ E, e.card = 2) (hpos : ∀ e ∈ E, 0 < relativeNullityOn S e)
    (hground : ∀ e ∈ E, e ⊆ G) (p : κ → R) (q : Finset κ → R) (t : R)
    (hdirect : ∀ I ∈ directFamilies S G, q I = ∏ x ∈ I, p x)
    (hcompressed : ∀ e ∈ E, ∀ A ∈ extensions S G e, q (e ∪ A) = q e * ∏ x ∈ A, p x) :
    retainedValue S G E q t = independentReference G p t + pairReference G E p q t -
      directDeficit S G p t - compressedDeficit S G E p q t := by
  classical
  have hd := direct_plus_deficit S G p t
  have he : (∑ e ∈ E, ∑ A ∈ extensions S G e, q e * t ^ 2 * familyTerm p t A) +
      compressedDeficit S G E p q t = pairReference G E p q t := by
    unfold compressedDeficit pairReference
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro e _he
    exact extensions_plus_failed S G e p q t
  rw [retained_decomposition S G E hcard hpos hground p q t hdirect hcompressed, ← hd, ← he]
  ring1

end PaperP1.RetainedReferenceIdentity
