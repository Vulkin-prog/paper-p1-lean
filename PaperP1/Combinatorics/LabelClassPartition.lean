module

public import PaperP1.Combinatorics.TargetComponentBudget
public import Mathlib.Data.Fintype.Basic

/-! # The actual nonzero coordinate label classes form a finite disjoint physical partition -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LabelClassPartition

open Finset

variable {V A : Type*} [Fintype V] [DecidableEq V] [DecidableEq A] [Zero A]

def part (ℓ : V → A) (a : A) : Finset V := univ.filter fun v ↦ ℓ v = a

def parts (ℓ : V → A) : Finset (Finset V) :=
  (TargetComponentBudget.labels ℓ univ).image (part ℓ)

omit [DecidableEq V] [Zero A] in
theorem mem_part (ℓ : V → A) (a : A) (v : V) : v ∈ part ℓ a ↔ ℓ v = a := by
  simp only [part, mem_filter, mem_univ, true_and]

omit [DecidableEq V] in
theorem part_nonempty (ℓ : V → A) {a : A} (ha : a ∈ TargetComponentBudget.labels ℓ univ) :
    (part ℓ a).Nonempty := by
  obtain ⟨v, _hv, hva⟩ := mem_image.mp (mem_erase.mp ha).2
  exact ⟨v, (mem_part ℓ a v).mpr hva⟩

theorem covers (ℓ : V → A) (v : V) (hv : ℓ v ≠ 0) : ∃ D ∈ parts ℓ, v ∈ D := by
  exact ⟨part ℓ (ℓ v), mem_image.mpr ⟨ℓ v, mem_erase.mpr ⟨hv, mem_image.mpr ⟨v, mem_univ _, rfl⟩⟩, rfl⟩,
    (mem_part _ _ _).mpr rfl⟩

theorem monochromatic (ℓ : V → A) (D : Finset V) (hD : D ∈ parts ℓ)
    (v : V) (hv : v ∈ D) (w : V) (hw : w ∈ D) : ℓ v = ℓ w := by
  obtain ⟨a, _ha, rfl⟩ := mem_image.mp hD
  exact ((mem_part _ _ _).mp hv).trans ((mem_part _ _ _).mp hw).symm

theorem disjoint_parts (ℓ : V → A) : (parts ℓ : Set (Finset V)).Pairwise Disjoint := by
  intro D hD E hE hDE
  obtain ⟨a, _ha, rfl⟩ := mem_image.mp hD
  obtain ⟨b, _hb, rfl⟩ := mem_image.mp hE
  apply disjoint_left.mpr
  intro v hva hvb
  have hab : a = b := ((mem_part _ _ _).mp hva).symm.trans ((mem_part _ _ _).mp hvb)
  exact hDE (congrArg (part ℓ) hab)

theorem part_size (ℓ : V → A) (K : ℕ)
    (hsize : ∀ a, a ≠ 0 → (part ℓ a).card ≤ K) : ∀ D ∈ parts ℓ, D.card ≤ K := by
  intro D hD
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hD
  exact hsize a (mem_erase.mp ha).1

theorem meeting_eq_image (ℓ : V → A) (T : Finset V) :
    TargetComponentBudget.meeting (parts ℓ) T = (TargetComponentBudget.labels ℓ T).image (part ℓ) := by
  ext D
  constructor
  · intro hD
    obtain ⟨hD, v, hv⟩ := mem_filter.mp hD
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hD
    obtain ⟨hvD, hvT⟩ := mem_inter.mp hv
    have hva := (mem_part ℓ a v).mp hvD
    exact mem_image.mpr ⟨a, mem_erase.mpr ⟨(mem_erase.mp ha).1, mem_image.mpr ⟨v, hvT, hva⟩⟩, rfl⟩
  · intro hD
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hD
    obtain ⟨ha0, v, hvT, hva⟩ := mem_erase.mp ha |>.imp_right mem_image.mp
    apply mem_filter.mpr
    exact ⟨mem_image.mpr ⟨a, mem_erase.mpr ⟨ha0, mem_image.mpr ⟨v, mem_univ _, hva⟩⟩, rfl⟩,
      v, mem_inter.mpr ⟨(mem_part _ _ _).mpr hva, hvT⟩⟩

theorem meeting_card (ℓ : V → A) (T : Finset V) :
    (TargetComponentBudget.meeting (parts ℓ) T).card = (TargetComponentBudget.labels ℓ T).card := by
  rw [meeting_eq_image]
  apply card_image_iff.mpr
  intro a ha b _hb hab
  obtain ⟨v, _hvT, hva⟩ := mem_image.mp (mem_erase.mp ha).2
  have hvb : v ∈ part ℓ b := hab ▸ (mem_part _ _ _).mpr hva
  exact hva.symm.trans ((mem_part _ _ _).mp hvb)

end PaperP1.LabelClassPartition
