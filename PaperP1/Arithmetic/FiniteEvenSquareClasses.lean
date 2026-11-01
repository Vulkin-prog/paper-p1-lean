module

public import PaperP1.Algebra.EvenImage
public import PaperP1.Arithmetic.ParityVector
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.Abel

/-! # Even square-class images of finite sets, unions and dilations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteEvenSquareClasses

open Finset PaperP1.Arithmetic

local instance finiteEvenPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def data (S : Finset ℕ) : S → (ℕ →₀ F₂) := fun n ↦ parityVec n.val

def space (S : Finset ℕ) : Submodule F₂ (ℕ →₀ F₂) := EvenImage.image (data S)

def Private (S : Finset ℕ) : Prop :=
  ∀ n ∈ S, ∃ p : ℕ, parityVec n p ≠ 0 ∧ ∀ m ∈ S, m ≠ n → parityVec m p = 0

def dilate (c : ℕ) (S : Finset ℕ) : Finset ℕ := S.image (fun n ↦ c * n)

def selected (S : Finset ℕ) (w : S → F₂) : Finset S := univ.filter fun n ↦ w n ≠ 0

theorem sum_eq_selected_card (S : Finset ℕ) (w : S → F₂) :
    (∑ n : S, w n) = ((selected S w).card : F₂) := by
  classical
  calc
    _ = ∑ n ∈ selected S w, (1 : F₂) := by
      rw [selected, sum_filter]
      apply sum_congr rfl
      intro n _
      have hbit : w n = 0 ∨ w n = 1 := by generalize w n = z; revert z; decide
      rcases hbit with hz | ho
      · simp only [hz, ne_eq, not_true_eq_false, ite_false]
      · norm_num [ho]
    _ = _ := by simp

theorem zero_sum_iff_even_selected (S : Finset ℕ) (w : S → F₂) :
    (∑ n : S, w n) = 0 ↔ Even (selected S w).card := by
  rw [sum_eq_selected_card, ZMod.natCast_eq_zero_iff, even_iff_two_dvd]

theorem Private.mono {S T : Finset ℕ} (hT : Private T) (hST : S ⊆ T) : Private S := by
  intro n hn
  obtain ⟨p, hp, hothers⟩ := hT n (hST hn)
  exact ⟨p, hp, fun m hm hmn ↦ hothers m (hST hm) hmn⟩

theorem space_eq_span (S : Finset ℕ) (a : ℕ) (ha : a ∈ S) :
    space S = Submodule.span F₂ ((fun n ↦ parityVec n - parityVec a) '' (S : Set ℕ)) := by
  rw [space, EvenImage.image_eq_span_differences (data S) (⟨a, ha⟩ : S)]
  congr 1
  ext z
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n.val, n.property, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨n, hn⟩, rfl⟩

theorem space_empty : space ∅ = ⊥ := by
  apply le_antisymm
  · intro z hz
    obtain ⟨w, _, hw⟩ := (EvenImage.mem_image_iff (data ∅) z).mp hz
    rw [EvenImage.combination_apply] at hw
    simpa using hw.symm
  · exact bot_le

theorem space_union (S T : Finset ℕ) (a : ℕ) (haS : a ∈ S) (haT : a ∈ T) :
    space (S ∪ T) = space S ⊔ space T := by
  rw [space_eq_span (S ∪ T) a (mem_union.mpr (Or.inl haS)), space_eq_span S a haS,
    space_eq_span T a haT, ← Submodule.span_union]
  simp only [coe_union, Set.image_union]

theorem space_dilate (S : Finset ℕ) {c : ℕ} (hc : 0 < c) (hS : ∀ n ∈ S, 0 < n) :
    space (dilate c S) = space S := by
  by_cases hne : S.Nonempty
  · obtain ⟨a, ha⟩ := hne
    have hca : c * a ∈ dilate c S := mem_image.mpr ⟨a, ha, rfl⟩
    rw [space_eq_span _ (c * a) hca, space_eq_span S a ha]
    congr 1
    ext z
    constructor
    · rintro ⟨n, hn, rfl⟩
      obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
      refine ⟨m, hm, ?_⟩
      change parityVec m - parityVec a = parityVec (c * m) - parityVec (c * a)
      rw [parityVec_mul hc.ne' (hS m hm).ne', parityVec_mul hc.ne' (hS a ha).ne']
      abel
    · rintro ⟨m, hm, rfl⟩
      refine ⟨c * m, mem_image.mpr ⟨m, hm, rfl⟩, ?_⟩
      change parityVec (c * m) - parityVec (c * a) = parityVec m - parityVec a
      rw [parityVec_mul hc.ne' (hS m hm).ne', parityVec_mul hc.ne' (hS a ha).ne']
      abel
  · have hempty : S = ∅ := not_nonempty_iff_eq_empty.mp hne
    subst S
    simp only [dilate, image_empty]

theorem coefficient_zero (S : Finset ℕ) (hS : Private S) (w : S → F₂)
    (hw : EvenImage.combination (data S) w = 0) (n : S) : w n = 0 := by
  obtain ⟨p, hp, hothers⟩ := hS n.val n.property
  have hcoord := congrArg (fun f : ℕ →₀ F₂ ↦ f p) hw
  rw [EvenImage.combination_apply] at hcoord
  change (∑ m : S, w m • parityVec m.val) p = 0 at hcoord
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul] at hcoord
  have hsum : (∑ m : S, w m * parityVec m.val p) = w n * parityVec n.val p := by
    apply sum_eq_single n
    · intro m _ hmn
      have hvals : m.val ≠ n.val := fun h ↦ hmn (Subtype.ext h)
      rw [hothers m.val m.property hvals, mul_zero]
    · simp only [mem_univ, not_true_eq_false, IsEmpty.forall_iff]
  rw [hsum] at hcoord
  exact (mul_eq_zero.mp hcoord).resolve_right hp

theorem combination_injective (S : Finset ℕ) (hS : Private S) :
    Function.Injective (EvenImage.combination (K := F₂) (data S)) := by
  intro w z hwz
  have hzero : EvenImage.combination (data S) (w - z) = 0 := by rw [map_sub, hwz, sub_self]
  funext n
  exact sub_eq_zero.mp (coefficient_zero S hS (w - z) hzero n)

theorem finrank_space (S : Finset ℕ) (hS : Private S) :
    Module.finrank F₂ (space S) = S.card - 1 := by
  change Module.finrank F₂ (EvenImage.image (K := F₂) (data S)) = _
  have h := EvenImage.finrank_of_injective (K := F₂) (data S) (combination_injective S hS)
  rw [Fintype.card_coe] at h
  exact h

end PaperP1.FiniteEvenSquareClasses
