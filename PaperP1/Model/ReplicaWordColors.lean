module

public import PaperP1.Combinatorics.ReplicaTupleIndex
public import PaperP1.Model.ColoredTupleMass
public import PaperP1.Model.ReplicaColorEmbedding

/-! # Ordered replica colors and exact identification of flattened joint and seed masses -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReplicaWordColors

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.ColoredPrimeSamples
  PaperP1.UniformFubini PaperP1.ReplicaTupleIndex

local instance replicaWordColorsTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance replicaWordColorsDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def word {κ : Type*} (r q : ℕ) (hr : 0 < r) (color : Fin r → κ) (n : ℕ) : Fin (q + 1) × κ :=
  if h : n < r + q * r then
    let p := (index r q).symm ⟨n, h⟩
    (p.1, color p.2)
  else (0, color ⟨0, hr⟩)

theorem word_index {κ : Type*} {r q : ℕ} (hr : 0 < r) (color : Fin r → κ)
    (j : Fin (q + 1)) (i : Fin r) :
    word r q hr color (index r q (j, i)).val = (j, color i) := by
  simp only [word, (index r q (j, i)).isLt, dite_true]
  change (((index r q).symm (index r q (j, i))).1,
    color ((index r q).symm (index r q (j, i))).2) = (j, color i)
  rw [Equiv.symm_apply_apply]

theorem word_first {κ : Type*} {r q : ℕ} (hr : 0 < r) (color : Fin r → κ) (i : Fin r) :
    word r q hr color i.val = (0, color i) := by
  have h := word_index (q := q) hr color 0 i
  rw [index_first] at h
  exact h

theorem flatten_event {κ : Type*} {r q M L : ℕ} (hr : 0 < r) (Y : ℕ)
    (color : Fin r → κ) (c : ℕ → Fin L → F₂) (t : Fin (q + 1) → Fin r → ℕ)
    (ω : Sample (Fin (q + 1) × κ) M) :
    ColoredTupleMass.event Y (word r q hr color) (fun _ ↦ c) (flatten t) ω ↔
      ∀ p : Fin (q + 1) × Fin r, start M Y (t p.1 p.2) L (p.1, color p.2) ω = c (t p.1 p.2) := by
  constructor
  · intro h p
    have hp := h (index r q p)
    rcases p with ⟨j, i⟩
    simpa only [flatten_apply, word_index] using hp
  · intro h i
    obtain ⟨p, rfl⟩ := (index r q).surjective i
    rcases p with ⟨j, i⟩
    simpa only [flatten_apply, word_index] using h (j, i)

theorem flattened_mass {κ : Type*} [Fintype κ] {r q : ℕ} (hr : 0 < r) (M Y L : ℕ)
    (color : Fin r → κ) (c : ℕ → Fin L → F₂) (t : Fin (q + 1) → Fin r → ℕ) :
    ColoredTupleMass.joint M Y L (word r q hr color) (fun _ ↦ c) (flatten t) =
      ColoredReplicaMass.jointProbability M Y L (fun p : Fin (q + 1) × Fin r ↦ t p.1 p.2)
        (fun p ↦ (p.1, color p.2)) (fun p ↦ c (t p.1 p.2)) := by
  unfold ColoredTupleMass.joint ColoredReplicaMass.jointProbability
  apply UniformFubini.congr
  intro ω
  simp only [flatten_event]
  by_cases h : ∀ p : Fin (q + 1) × Fin r,
    start M Y (t p.1 p.2) L (p.1, color p.2) ω = c (t p.1 p.2) <;> simp only [h, ite_false]

theorem seed_mass {κ : Type*} [Fintype κ] {r q : ℕ} (hr : 0 < r) (M Y L : ℕ)
    (color : Fin r → κ) (c : ℕ → Fin L → F₂) (x : Fin r → ℕ) :
    ColoredTupleMass.joint M Y L (word r q hr color) (fun _ ↦ c) x =
      ColoredReplicaMass.jointProbability M Y L x color (fun i ↦ c (x i)) := by
  have heq : ColoredTupleMass.joint M Y L (word r q hr color) (fun _ ↦ c) x =
      ColoredReplicaMass.jointProbability M Y L x (fun i ↦ ((0 : Fin (q + 1)), color i)) (fun i ↦ c (x i)) := by
    unfold ColoredTupleMass.joint ColoredReplicaMass.jointProbability
    apply UniformFubini.congr
    intro ω
    simp only [ColoredTupleMass.event, word_first]
    by_cases h : ∀ i, start M Y (x i) L ((0 : Fin (q + 1)), color i) ω = c (x i) <;>
      simp only [h, ite_false]
  rw [heq]
  exact ReplicaColorEmbedding.joint_mass_eq M Y L x color (fun i ↦ c (x i))
    (fun k ↦ ((0 : Fin (q + 1)), k)) (fun _ _ h ↦ (Prod.mk.inj h).2)

end PaperP1.ReplicaWordColors
