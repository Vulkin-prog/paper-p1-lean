module

public import PaperP1.Model.HomogeneousRunMass
public import PaperP1.Affine.PrimitiveRelations
public import PaperP1.Affine.PrimitiveNullity
public import PaperP1.Arithmetic.WindowPairCentreBlocks

/-! # Literal primitive families above one compressed pair

The first effective space is the full span of the two source windows.
Primitivity concerns this compressed family, rather than the dependent
original source windows separately. Homogeneous weights retain incompatible
affine prescriptions.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairCompressedPrimitiveFamilies

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
  PaperP1.SubspaceFamilyRank

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def spaces {t : ℕ} (xy : ℕ × ℕ) (L : ℕ) (z : Fin t → ℕ) :
    Fin (t + 1) → Submodule F₂ (ℕ →₀ F₂) :=
  Fin.cons (squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L)
    (fun i ↦ squareClassSpace (z i) L)

instance spacesFintype {t : ℕ} (xy : ℕ × ℕ) (L : ℕ) (z : Fin t → ℕ)
    (i : Fin (t + 1)) : Fintype (spaces xy L z i) := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change Fintype ↥(squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L)
    let f : squareClassSpace xy.1 L × squareClassSpace xy.2 L →
        ↥(squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L) :=
      fun p ↦ ⟨p.1.val + p.2.val, Submodule.add_mem_sup p.1.property p.2.property⟩
    exact Fintype.ofSurjective f (by
      rintro ⟨u, hu⟩
      obtain ⟨v, hv, w, hw, hvw⟩ := Submodule.mem_sup.mp hu
      exact ⟨(⟨v, hv⟩, ⟨w, hw⟩), Subtype.ext hvw⟩)
  · exact inferInstanceAs (Fintype (squareClassSpace (z j) L))

def nullity {t : ℕ} (xy : ℕ × ℕ) (L : ℕ) (z : Fin t → ℕ) : ℕ :=
  relativeNullityOn (spaces xy L z) univ

def Primitive {t : ℕ} (xy : ℕ × ℕ) (L : ℕ) (z : Fin t → ℕ) : Prop :=
  0 < nullity xy L z ∧
    ∀ J : Finset (Fin (t + 1)), J ⊂ univ → relativeNullityOn (spaces xy L z) J = 0

def family {t : ℕ} (xy : ℕ × ℕ) (z : Fin t → ℕ) : Finset ℕ :=
  {xy.1, xy.2} ∪ univ.image z

theorem span_eq {t : ℕ} (xy : ℕ × ℕ) (L : ℕ) (z : Fin t → ℕ) :
    span (spaces xy L z) univ = span (fun x ↦ squareClassSpace x L) (family xy z) := by
  have hleft : span (spaces xy L z) univ =
      (squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L) ⊔
        ⨆ i, squareClassSpace (z i) L := by
    apply le_antisymm
    · refine iSup_le fun i ↦ ?_
      refine Fin.cases ?_ (fun j ↦ ?_) i.val
      · exact le_sup_left
      · exact le_sup_of_le_right (le_iSup (fun j ↦ squareClassSpace (z j) L) j)
    · refine sup_le (local_le_span (spaces xy L z) univ (mem_univ 0)) ?_
      exact iSup_le fun j ↦ local_le_span (spaces xy L z) univ (mem_univ j.succ)
  rw [hleft, family, PaperP1.RetainedNullity.span_union,
    PaperP1.RetainedNullity.span_pair, span_image]
  congr 1
  simp only [span, iSup_subtype, mem_univ, iSup_pos]

theorem rank_add_nullity {N t L : ℕ} (xy : ℕ × ℕ) (z : Fin t → ℕ)
    (hz : ∀ i, z i ∈ RegularStarts.regularStarts N L) :
    rank (fun x ↦ squareClassSpace x L) (family xy z) + nullity xy L z =
      Module.finrank F₂ ↥(squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L) + t * L := by
  have h := rank_add_nullity_on (spaces xy L z) univ
  rw [show rank (spaces xy L z) univ =
      rank (fun x ↦ squareClassSpace x L) (family xy z) by rw [rank, span_eq]; rfl] at h
  change _ + nullity xy L z = _ at h
  rw [Fin.sum_univ_succ] at h
  change _ + nullity xy L z =
    Module.finrank F₂ ↥(squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L) +
      ∑ i, Module.finrank F₂ (squareClassSpace (z i) L) at h
  simpa only [fun i ↦ (RegularStarts.mem_regularStarts.mp (hz i)).2,
    sum_const, card_univ, Fintype.card_fin, smul_eq_mul] using h

theorem weight_factor {N t L : ℕ} (xy : ℕ × ℕ) (z : Fin t → ℕ)
    (hz : ∀ i, z i ∈ RegularStarts.regularStarts N L) :
    HomogeneousRunMass.probability L (family xy z) =
      HomogeneousRunMass.probability L {xy.1, xy.2} *
        ((2 ^ L : ℝ)⁻¹) ^ t * (2 ^ nullity xy L z : ℝ) := by
  have h := rank_add_nullity xy z hz
  have he : (2 ^ rank (fun x ↦ squareClassSpace x L) (family xy z) : ℝ) *
      (2 ^ nullity xy L z : ℝ) =
      (2 ^ Module.finrank F₂ ↥(squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L) : ℝ) *
        (2 ^ L : ℝ) ^ t := by
    rw [← pow_add, h, pow_add, Nat.mul_comm t L, pow_mul]
  rw [HomogeneousRunMass.probability_rank, HomogeneousRunMass.probability_rank,
    rank, rank, PaperP1.RetainedNullity.span_pair]
  rw [inv_pow]
  field_simp
  exact he.symm

theorem primitive_nullity_le {t L : ℕ} (xy : ℕ × ℕ) (z : Fin t → ℕ)
    (hp : Primitive xy L z) (i : Fin t) (hi : 0 < z i) : nullity xy L z ≤ L := by
  have h := PrimitiveNullity.minimal_bound (spaces xy L z) univ hp.2 i.succ (mem_univ _)
  exact h.trans (LocalRunRank.squareClass_rank_le (z i) L hi)

theorem full_relation {t L : ℕ} (xy : ℕ × ℕ) (z : Fin t → ℕ)
    (hp : Primitive xy L z) :
    ∃ u : Fin (t + 1) → (ℕ →₀ F₂),
      (∀ i, u i ∈ spaces xy L z i ∧ u i ≠ 0) ∧ ∑ i, u i = 0 := by
  classical
  obtain ⟨s, hs⟩ := PrimitiveRelations.full_relation_of_minimal_nullity
    (spaces xy L z) univ hp.1 hp.2
  let u := fun i : Fin (t + 1) ↦ (s ⟨i, mem_univ i⟩ : ℕ →₀ F₂)
  refine ⟨u, ?_, ?_⟩
  · intro i
    refine ⟨(s ⟨i, mem_univ i⟩).property, ?_⟩
    intro hi
    exact hs.1 ⟨i, mem_univ i⟩ (Subtype.ext hi)
  · have hsum := sum_coe_sort (univ : Finset (Fin (t + 1))) u
    calc
      _ = ∑ i : (univ : Finset (Fin (t + 1))), u i.val := hsum.symm
      _ = 0 := hs.2

end PaperP1.PairCompressedPrimitiveFamilies
