module

public import PaperP1.Model.ColoredReplicaMass

/-! # Independent color copies realize every product of replica block probabilities -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReplicaCopyBlocks

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.ColoredPrimeSamples
  PaperP1.ColoredReplicaMass PaperP1.UniformFubini

local instance replicaCopyBlocksDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem block_eq {ι κ J : Type*} {M : ℕ} (Y L : ℕ) (t : J → ι → ℕ)
    (color : ι → κ) (c : ℕ → Fin L → F₂) (j : J) (k : κ) (σ : SampleSpace M) :
    blockProbability Y L (fun p : J × ι ↦ t p.1 p.2) (fun p ↦ (p.1, color p.2))
      (fun p ↦ c (t p.1 p.2)) (j, k) σ =
      blockProbability Y L (t j) color (fun i ↦ c (t j i)) k σ := by
  unfold blockProbability
  apply UniformFubini.congr
  intro τ
  have hevent : (∀ p : J × ι, (p.1, color p.2) = (j, k) →
      startSystem M (t p.1 p.2) L (glue Y σ τ) = c (t p.1 p.2)) ↔
      ∀ i, color i = k → startSystem M (t j i) L (glue Y σ τ) = c (t j i) := by
    constructor
    · intro h i hi
      exact h (j, i) (Prod.ext rfl hi)
    · intro h p hp
      rcases p with ⟨j', i⟩
      obtain ⟨hj, hk⟩ := Prod.mk.inj hp
      change j' = j at hj
      subst j'
      exact h i hk
  simp only [hevent]

theorem product_blocks {ι κ J : Type*} [Fintype κ] [Fintype J] {M : ℕ} (Y L : ℕ)
    (t : J → ι → ℕ) (color : ι → κ) (c : ℕ → Fin L → F₂) (σ : SampleSpace M) :
    (∏ j, ∏ k, blockProbability Y L (t j) color (fun i ↦ c (t j i)) k σ) =
      ∏ p : J × κ, blockProbability Y L (fun a : J × ι ↦ t a.1 a.2)
        (fun a ↦ (a.1, color a.2)) (fun a ↦ c (t a.1 a.2)) p σ := by
  rw [Fintype.prod_prod_type]
  simp_rw [block_eq]

theorem averaged_product {ι κ J : Type*} [Fintype κ] [Fintype J] (M Y L : ℕ)
    (t : J → ι → ℕ) (color : ι → κ) (c : ℕ → Fin L → F₂) :
    average (fun σ : SampleSpace M ↦ ∏ j, ∏ k, blockProbability Y L (t j) color (fun i ↦ c (t j i)) k σ) =
      jointProbability M Y L (fun a : J × ι ↦ t a.1 a.2)
        (fun a ↦ (a.1, color a.2)) (fun a ↦ c (t a.1 a.2)) := by
  simp_rw [product_blocks]
  exact replica_identity M Y L _ _ _

theorem joint_nonneg {ι κ : Type*} [Fintype κ] (M Y L : ℕ)
    (x : ι → ℕ) (color : ι → κ) (b : ι → Fin L → F₂) :
    0 ≤ jointProbability M Y L x color b := by
  apply UniformFubini.nonneg
  intro ω
  split_ifs <;> norm_num

end PaperP1.ReplicaCopyBlocks
