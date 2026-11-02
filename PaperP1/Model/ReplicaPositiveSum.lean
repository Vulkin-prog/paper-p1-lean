module

public import PaperP1.Model.ReplicaCopyBlocks
public import PaperP1.Model.ReplicaWordColors

/-! # Actual positive replica sums and exact expansions of every fixed integer moment -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReplicaPositiveSum

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.ColoredReplicaMass
  PaperP1.UniformFubini PaperP1.Algebra PaperP1.ReplicaTupleIndex

variable {κ : Type*} [Fintype κ] {r : ℕ}

def randomSum {M : ℕ} (Y L : ℕ) (color : Fin r → κ) (c : ℕ → Fin L → F₂)
    (A : Finset (Fin r → ℕ)) (w : (Fin r → ℕ) → ℝ) (σ : SampleSpace M) : ℝ :=
  ∑ x ∈ A, w x * ∏ k, blockProbability Y L x color (fun i ↦ c (x i)) k σ

theorem first_moment (M Y L : ℕ) (color : Fin r → κ) (c : ℕ → Fin L → F₂)
    (A : Finset (Fin r → ℕ)) (w : (Fin r → ℕ) → ℝ) :
    average (randomSum Y L color c A w : SampleSpace M → ℝ) =
      ∑ x ∈ A, w x * jointProbability M Y L x color (fun i ↦ c (x i)) := by
  unfold randomSum average
  rw [finiteExpectation_sum]
  apply sum_congr rfl
  intro x _
  rw [finiteExpectation_const_mul]
  congr 1
  exact replica_identity M Y L x color (fun i ↦ c (x i))

theorem moment_expansion (M Y L q : ℕ) (color : Fin r → κ) (c : ℕ → Fin L → F₂)
    (A : Finset (Fin r → ℕ)) (w : (Fin r → ℕ) → ℝ) :
    average (fun σ : SampleSpace M ↦ (randomSum Y L color c A w σ) ^ (q + 1)) =
      ∑ t : Fin (q + 1) → A, (∏ j, w (t j).val) *
        jointProbability M Y L (fun p : Fin (q + 1) × Fin r ↦ (t p.1).val p.2)
          (fun p ↦ (p.1, color p.2)) (fun p ↦ c ((t p.1).val p.2)) := by
  classical
  have hexp (σ : SampleSpace M) : (randomSum Y L color c A w σ) ^ (q + 1) =
      ∑ t : Fin (q + 1) → A, (∏ j, w (t j).val) *
        ∏ j, ∏ k, blockProbability Y L (t j).val color (fun i ↦ c ((t j).val i)) k σ := by
    unfold randomSum
    rw [← sum_coe_sort A, Fintype.sum_pow]
    simp only [prod_mul_distrib]
  simp_rw [hexp]
  unfold average
  rw [finiteExpectation_sum]
  apply sum_congr rfl
  intro t _
  rw [finiteExpectation_const_mul]
  congr 1
  exact ReplicaCopyBlocks.averaged_product M Y L (fun j ↦ (t j).val) color c

theorem flattened_moment (M Y L q : ℕ) (hr : 0 < r) (color : Fin r → κ)
    (c : ℕ → Fin L → F₂) (A : Finset (Fin r → ℕ)) (w : (Fin r → ℕ) → ℝ) :
    average (fun σ : SampleSpace M ↦ (randomSum Y L color c A w σ) ^ (q + 1)) =
      ∑ t : Fin (q + 1) → A, (∏ j, w (t j).val) *
        ColoredTupleMass.joint M Y L (ReplicaWordColors.word r q hr color) (fun _ ↦ c)
          (flatten (fun j ↦ (t j).val)) := by
  rw [moment_expansion]
  apply sum_congr rfl
  intro t _
  congr 1
  exact (ReplicaWordColors.flattened_mass hr M Y L color c (fun j ↦ (t j).val)).symm

theorem first_moment_nonneg (M Y L : ℕ) (color : Fin r → κ) (c : ℕ → Fin L → F₂)
    (A : Finset (Fin r → ℕ)) (w : (Fin r → ℕ) → ℝ) (hw : ∀ x ∈ A, 0 ≤ w x) :
    0 ≤ average (randomSum Y L color c A w : SampleSpace M → ℝ) := by
  rw [first_moment]
  exact sum_nonneg fun x hx ↦ mul_nonneg (hw x hx) (ReplicaCopyBlocks.joint_nonneg M Y L x color _)

end PaperP1.ReplicaPositiveSum
