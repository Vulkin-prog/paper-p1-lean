module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Linarith

/-! # Three disjoint offset families supply the actual distinct grid points needed for rational interpolation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DisjointOffsetGrid

open Finset

variable {ι : Type*}

def points (A : Finset ι) (I : ι → Finset ℤ) (j : ι → ℤ) : Finset (ℤ × ℤ) :=
  A.biUnion fun ν ↦ (I ν).image fun x ↦ (x, j ν)

theorem fst_injective (A : Finset ι) (I : ι → Finset ℤ) (j : ι → ℤ)
    (hdisj : (A : Set ι).PairwiseDisjoint I) : Set.InjOn (Prod.fst : ℤ × ℤ → ℤ) (points A I j : Set (ℤ × ℤ)) := by
  classical
  rintro u hu v hv huv
  obtain ⟨ν, hν, himage⟩ := mem_biUnion.mp hu
  obtain ⟨x, hx, rfl⟩ := mem_image.mp himage
  obtain ⟨μ, hμ, himage'⟩ := mem_biUnion.mp hv
  obtain ⟨y, hy, rfl⟩ := mem_image.mp himage'
  change x = y at huv
  have hνμ : ν = μ := by
    by_contra hne
    exact disjoint_left.mp (hdisj hν hμ hne) hx (huv ▸ hy)
  exact Prod.ext huv (congrArg j hνμ)

theorem card_points (A : Finset ι) (I : ι → Finset ℤ) (j : ι → ℤ) (a : ℕ)
    (hdisj : (A : Set ι).PairwiseDisjoint I) (hcard : ∀ ν ∈ A, (I ν).card = a) :
    (points A I j).card = A.card * a := by
  classical
  have hd : (A : Set ι).PairwiseDisjoint (fun ν ↦ (I ν).image fun x ↦ (x, j ν)) := by
    intro ν hν μ hμ hne
    apply disjoint_left.mpr
    intro z hzν hzμ
    obtain ⟨x, hx, hxz⟩ := mem_image.mp hzν
    obtain ⟨y, hy, hyz⟩ := mem_image.mp hzμ
    have hxy : x = y := congrArg Prod.fst (hxz.trans hyz.symm)
    exact disjoint_left.mp (hdisj hν hμ hne) hx (hxy ▸ hy)
  rw [points, card_biUnion hd]
  calc
    (∑ ν ∈ A, ((I ν).image fun x ↦ (x, j ν)).card) = ∑ _ν ∈ A, a :=
      sum_congr rfl fun ν hν ↦ (card_image_of_injective _ (fun _ _ h ↦ congrArg Prod.fst h)).trans (hcard ν hν)
    _ = _ := by simp

theorem select (A : Finset ι) (I : ι → Finset ℤ) (j : ι → ℤ) (a : ℕ) (ha : 0 < a)
    (hA : 3 ≤ A.card) (hdisj : (A : Set ι).PairwiseDisjoint I) (hcard : ∀ ν ∈ A, (I ν).card = a) :
    ∃ x y : Fin (2 * a + 1) → ℤ, Function.Injective x ∧
      ∀ t, ∃ ν ∈ A, x t ∈ I ν ∧ y t = j ν := by
  classical
  have hc : 2 * a + 1 ≤ (points A I j).card := by
    rw [card_points A I j a hdisj hcard]
    have h3a := Nat.mul_le_mul_right a hA
    omega
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin (2 * a + 1)) (s := points A I j) (by simpa only [Fintype.card_fin] using hc)
  have hem (t) : e t ∈ points A I j := he ⟨t, rfl⟩
  refine ⟨fun t ↦ (e t).1, fun t ↦ (e t).2, ?_, ?_⟩
  · intro t u htu
    exact e.injective (fst_injective A I j hdisj (hem t) (hem u) htu)
  · intro t
    obtain ⟨ν, hν, himage⟩ := mem_biUnion.mp (hem t)
    obtain ⟨x, hx, heq⟩ := mem_image.mp himage
    have hfirst : x = (e t).1 := congrArg Prod.fst heq
    refine ⟨ν, hν, ?_, (congrArg Prod.snd heq).symm⟩
    change (e t).1 ∈ I ν
    rw [← hfirst]
    exact hx

variable [DecidableEq ι]

theorem three_survivors (A bad : Finset ι) (E e : ℕ) (he : e ≤ E)
    (hA : 4 * (E + 1) ^ 2 ≤ A.card) (hbad : bad.card ≤ 2 * e ^ 2) : 3 ≤ (A \ bad).card := by
  classical
  have he2 : e ^ 2 ≤ E ^ 2 := Nat.pow_le_pow_left he 2
  have hgap : 2 * e ^ 2 + 3 ≤ 4 * (E + 1) ^ 2 := by nlinarith
  have hgood : A.card ≤ (A \ bad).card + bad.card := card_le_card_sdiff_add_card
  omega

theorem select_survivors (A bad : Finset ι) (I : ι → Finset ℤ) (j : ι → ℤ)
    (a E e : ℕ) (ha : 0 < a) (he : e ≤ E) (hA : 4 * (E + 1) ^ 2 ≤ A.card)
    (hbad : bad.card ≤ 2 * e ^ 2) (hdisj : (A : Set ι).PairwiseDisjoint I)
    (hcard : ∀ ν ∈ A, (I ν).card = a) :
    ∃ x y : Fin (2 * a + 1) → ℤ, Function.Injective x ∧
      ∀ t, ∃ ν ∈ A \ bad, x t ∈ I ν ∧ y t = j ν := by
  classical
  exact select (A \ bad) I j a ha (three_survivors A bad E e he hA hbad)
    (Set.Pairwise.mono sdiff_subset hdisj) (fun ν hν ↦ hcard ν (mem_sdiff.mp hν).1)

end PaperP1.DisjointOffsetGrid
