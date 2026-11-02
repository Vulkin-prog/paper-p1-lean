module

public import PaperP1.Model.ColoredReplicaMass

/-! # Adding unused independent colors preserves every actual replica joint mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReplicaColorEmbedding

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.ColoredReplicaMass PaperP1.UniformFubini

local instance replicaColorEmbeddingDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem used_block {ι κ κ' : Type*} {M : ℕ} (Y L : ℕ) (x : ι → ℕ)
    (color : ι → κ) (b : ι → Fin L → F₂) (e : κ → κ') (he : Function.Injective e)
    (k : κ) (σ : SampleSpace M) :
    blockProbability Y L x (fun i ↦ e (color i)) b (e k) σ = blockProbability Y L x color b k σ := by
  unfold blockProbability
  simp_rw [he.eq_iff]

theorem unused_block {ι κ κ' : Type*} {M : ℕ} (Y L : ℕ) (x : ι → ℕ)
    (color : ι → κ) (b : ι → Fin L → F₂) (e : κ → κ')
    (k : κ') (hk : k ∉ Set.range e) (σ : SampleSpace M) :
    blockProbability Y L x (fun i ↦ e (color i)) b k σ = 1 := by
  have hi (i : ι) : e (color i) ≠ k := fun h ↦ hk ⟨color i, h⟩
  unfold blockProbability
  simp only [hi, IsEmpty.forall_iff, implies_true, ite_true, UniformFubini.constant]

theorem joint_mass_eq {ι κ κ' : Type*} [Fintype κ] [Fintype κ'] (M Y L : ℕ) (x : ι → ℕ)
    (color : ι → κ) (b : ι → Fin L → F₂) (e : κ → κ') (he : Function.Injective e) :
    jointProbability M Y L x (fun i ↦ e (color i)) b = jointProbability M Y L x color b := by
  rw [← replica_identity, ← replica_identity]
  apply UniformFubini.congr
  intro σ
  exact (Fintype.prod_of_injective e he (fun k ↦ blockProbability Y L x color b k σ)
    (fun k ↦ blockProbability Y L x (fun i ↦ e (color i)) b k σ)
    (fun k hk ↦ unused_block Y L x color b e k hk σ)
    (fun k ↦ (used_block Y L x color b e he k σ).symm)).symm

end PaperP1.ReplicaColorEmbedding
