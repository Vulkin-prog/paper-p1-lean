module

public import PaperP1.Combinatorics.ZeroSumFreeRepresentations
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Interval.Finset.Nat

/-! # Bounded label multiplicity gives a finite pool of physical short supports

The bound deliberately permits every subset of each label fibre. Its
constant is larger than the injective-choice bound but uniform in all
physical labels and sufficient when support size is fixed before N.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PhysicalLabelSupportCount

open Finset PaperP1.ZeroSumFreeRepresentations

variable {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]

def fibre (L : V → W) (a : W) : Finset V := univ.filter fun v ↦ L v = a

def preimage (L : V → W) (A : Finset W) : Finset V := univ.filter fun v ↦ L v ∈ A

def lifts (L : V → W) (F : Finset (Finset W)) : Finset (Finset V) :=
  univ.powerset.filter fun A ↦ A.image L ∈ F

theorem preimage_eq_biUnion (L : V → W) (A : Finset W) :
    preimage L A = A.biUnion (fibre L) := by
  ext v
  simp only [preimage, fibre, mem_filter, mem_univ, true_and, mem_biUnion]
  exact ⟨fun h ↦ ⟨L v, h, rfl⟩, fun ⟨a, ha, heq⟩ ↦ heq.symm ▸ ha⟩

theorem preimage_card (L : V → W) (A : Finset W) (K : ℕ)
    (hK : ∀ a ∈ A, (fibre L a).card ≤ K) : (preimage L A).card ≤ A.card * K := by
  rw [preimage_eq_biUnion]
  exact card_biUnion_le.trans ((sum_le_sum hK).trans_eq (by simp))

theorem lift_cover (L : V → W) (F : Finset (Finset W)) :
    lifts L F ⊆ F.biUnion (fun A ↦ (preimage L A).powerset) := by
  intro B hB
  have hBF := (mem_filter.mp hB).2
  refine mem_biUnion.mpr ⟨B.image L, hBF, mem_powerset.mpr ?_⟩
  intro v hv
  exact mem_filter.mpr ⟨mem_univ _, mem_image.mpr ⟨v, hv, rfl⟩⟩

theorem lifts_card (L : V → W) (F : Finset (Finset W)) (d K : ℕ)
    (hF : ∀ A ∈ F, A.card ≤ d ∧ ∀ a ∈ A, (fibre L a).card ≤ K) :
    (lifts L F).card ≤ F.card * 2 ^ (d * K) := by
  calc
    _ ≤ (F.biUnion (fun A ↦ (preimage L A).powerset)).card := card_le_card (lift_cover L F)
    _ ≤ ∑ A ∈ F, (preimage L A).powerset.card := card_biUnion_le
    _ ≤ ∑ _A ∈ F, 2 ^ (d * K) := by
      apply sum_le_sum
      intro A hA
      rw [card_powerset]
      exact Nat.pow_le_pow_right (by norm_num : 0 < 2)
        ((preimage_card L A K (hF A hA).2).trans (Nat.mul_le_mul_right K (hF A hA).1))
    _ = _ := by simp

omit [Fintype V] in
theorem injective_lift (L : V → W) (A : Finset V) (B : Finset W) (hB : B ⊆ A.image L) :
    ∃ D ⊆ A, D.image L = B ∧ D.card = B.card ∧ Set.InjOn L (D : Set V) := by
  classical
  have hex : ∀ b : B, ∃ v ∈ A, L v = b.val := fun b ↦ mem_image.mp (hB b.property)
  choose f hfA hfL using hex
  have hfinj : Function.Injective f := by
    intro b c hbc
    apply Subtype.ext
    simpa only [hfL] using congrArg L hbc
  let D := univ.image f
  have hDsub : D ⊆ A := by
    intro v hv
    obtain ⟨b, _, rfl⟩ := mem_image.mp hv
    exact hfA b
  have hDimage : D.image L = B := by
    ext b
    constructor
    · intro hb
      obtain ⟨v, hv, hvb⟩ := mem_image.mp hb
      obtain ⟨c, _, rfl⟩ := mem_image.mp hv
      rw [hfL] at hvb
      exact hvb ▸ c.property
    · intro hb
      exact mem_image.mpr ⟨f ⟨b, hb⟩, mem_image.mpr ⟨⟨b, hb⟩, mem_univ _, rfl⟩, hfL ⟨b, hb⟩⟩
  have hDcard : D.card = B.card := by
    rw [card_image_of_injective _ hfinj, card_univ, Fintype.card_coe]
  refine ⟨D, hDsub, hDimage, hDcard, ?_⟩
  apply injOn_of_card_image_eq
  rw [hDimage, hDcard]

variable [AddCommGroup W]

def supportPool (L : V → W) (S : Finset W) (d : ℕ) (α : W) : Finset (Finset V) :=
  (Icc 1 d).biUnion fun j ↦ lifts L (representations S j α)

def supportBound (d t K : ℕ) : ℕ :=
  ∑ j ∈ Icc 1 d, j.factorial * (t - 1) ^ (j - 1) * 2 ^ (j * K)

theorem representation_lifts_card (L : V → W) (S : Finset W) (d t K j : ℕ)
    (hno : NoDisjointSums S d t) (hK : ∀ a ∈ S, (fibre L a).card ≤ K)
    (hj : 1 ≤ j) (hjd : j ≤ d) (α : W) (hα : α ≠ 0) :
    (lifts L (representations S j α)).card ≤
      j.factorial * (t - 1) ^ (j - 1) * 2 ^ (j * K) := by
  have hF : ∀ A ∈ representations S j α, A.card ≤ j ∧ ∀ a ∈ A, (fibre L a).card ≤ K := by
    intro A hA
    obtain ⟨hAS, hcard, _, _⟩ := mem_representations.mp hA
    exact ⟨hcard.le, fun a ha ↦ hK a (hAS ha)⟩
  exact (lifts_card L _ j K hF).trans
    (Nat.mul_le_mul_right _ (representations_card_le S d t hno j hj hjd α hα))

theorem supportPool_card (L : V → W) (S : Finset W) (d t K : ℕ)
    (hno : NoDisjointSums S d t) (hK : ∀ a ∈ S, (fibre L a).card ≤ K)
    (α : W) (hα : α ≠ 0) : (supportPool L S d α).card ≤ supportBound d t K := by
  unfold supportPool supportBound
  apply card_biUnion_le.trans
  apply sum_le_sum
  intro j hj
  exact representation_lifts_card L S d t K j hno hK (mem_Icc.mp hj).1 (mem_Icc.mp hj).2 α hα

end PaperP1.PhysicalLabelSupportCount
