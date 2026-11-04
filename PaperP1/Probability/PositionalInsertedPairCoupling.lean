module

public import PaperP1.Probability.PositionalInsertedPair
public import PaperP1.Probability.PositionalKernelComposition
public import PaperP1.Probability.PositionalBackgroundDeletion
public import PaperP1.Probability.PositionalPoissonBadEvents

/-! # Actual once/isolation coupling after one marked pair arrival -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalInsertedPairCoupling

open Finset PaperP1.PositionalFiniteLaw PaperP1.FiniteConvolutionAlgebra
  PaperP1.CompletedPositionalLaw PaperP1.PositivePositionalConvolution
  PaperP1.PositionalPairDeletion PaperP1.PositionalDeletionKernels
  PaperP1.PositionalInsertedPair PaperP1.PositionalPoissonObservables

variable {ι : Type*}

local instance insertedPairCouplingDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem good_input_properties (E : Finset (Finset ι)) (e : Finset ι) (v : Configuration ι)
    (h : ¬ ((activeEdges E v).Nonempty ∨ 0 < subsetCount (touchingVertices E e) v)) :
    activeEdges E v = ∅ ∧ ∀ x ∈ touchingVertices E e, v x = 0 := by
  obtain ⟨hno, hzero⟩ := not_or.mp h
  refine ⟨not_nonempty_iff_eq_empty.mp hno, ?_⟩
  intro x hx
  have hz : subsetCount (touchingVertices E e) v = 0 := by omega
  have hxle : v x ≤ ∑ y ∈ touchingVertices E e, v y :=
    single_le_sum (fun y _hy ↦ Nat.zero_le (v y)) hx
  rw [← subsetCount_eq_sum, hz] at hxle
  omega

theorem once_bound (E : Finset (Finset ι)) (e : Finset ι)
    (he : e ∈ E) (hE : ∀ f ∈ E, f.card = 2) (ν : Space ι) (hν : ∀ v, 0 ≤ coeff v ν) :
    ‖once E (ofFinite (atom (edgeVector e)) * ν) - ν‖ ≤
      2 * ∑' v : Configuration ι,
        if (activeEdges E v).Nonempty ∨ 0 < subsetCount (touchingVertices E e) v then coeff v ν else 0 := by
  have hleft : once E (ofFinite (atom (edgeVector e)) * ν) =
      PositionalMarkovKernel.action (fun v ↦ onceKernel E (v + edgeVector e))
        (fun v ↦ onceKernel_isProbability E (v + edgeVector e)) ν := by
    rw [← PositionalKernelComposition.push_shift]
    exact PositionalKernelComposition.action_push _ _ _ ν
  have hh := PositionalKernelCoupling.event_bound
    (fun v ↦ onceKernel E (v + edgeVector e)) (fun v ↦ ofFinite (atom v))
    (fun v ↦ onceKernel_isProbability E (v + edgeVector e))
    PositionalDeterministicMap.atom_isProbability ν hν
    (fun v ↦ (activeEdges E v).Nonempty ∨ 0 < subsetCount (touchingVertices E e) v)
    (fun v hv ↦ Or.inr (onceKernel_inserted_pair E e v he hE
      (good_input_properties E e v hv).1 (good_input_properties E e v hv).2))
  convert hh using 1
  · rw [hleft, PositionalBackgroundDeletion.identity_action]
  · apply congrArg (fun r : ℝ ↦ 2 * r)
    apply tsum_congr
    intro v
    by_cases hv : (activeEdges E v).Nonempty ∨ 0 < subsetCount (touchingVertices E e) v
    · simp only [ite_eq_left hv]
    · simp only [ite_eq_right hv]

theorem isolated_bound (E : Finset (Finset ι)) (e : Finset ι)
    (he : e ∈ E) (hE : ∀ f ∈ E, f.card = 2) (ν : Space ι) (hν : ∀ v, 0 ≤ coeff v ν) :
    ‖isolated E (ofFinite (atom (edgeVector e)) * ν) - ν‖ ≤
      2 * ∑' v : Configuration ι,
        if (activeEdges E v).Nonempty ∨ 0 < subsetCount (touchingVertices E e) v then coeff v ν else 0 := by
  have hleft : isolated E (ofFinite (atom (edgeVector e)) * ν) =
      PositionalMarkovKernel.action (fun v ↦ ofFinite (atom (isolate E (v + edgeVector e))))
        (fun v ↦ PositionalDeterministicMap.atom_isProbability (isolate E (v + edgeVector e))) ν := by
    rw [← PositionalKernelComposition.push_shift]
    exact PositionalKernelComposition.action_push (fun v ↦ ofFinite (atom (isolate E v)))
      (fun v ↦ PositionalDeterministicMap.atom_isProbability (isolate E v))
      (fun v ↦ v + edgeVector e) ν
  have hh := PositionalKernelCoupling.event_bound
    (fun v ↦ ofFinite (atom (isolate E (v + edgeVector e)))) (fun v ↦ ofFinite (atom v))
    (fun v ↦ PositionalDeterministicMap.atom_isProbability (isolate E (v + edgeVector e)))
    PositionalDeterministicMap.atom_isProbability ν hν
    (fun v ↦ (activeEdges E v).Nonempty ∨ 0 < subsetCount (touchingVertices E e) v)
    (fun v hv ↦ Or.inr (by rw [isolate_inserted_pair E e v he hE
      (good_input_properties E e v hv).1 (good_input_properties E e v hv).2]))
  convert hh using 1
  · rw [hleft, PositionalBackgroundDeletion.identity_action]
  · apply congrArg (fun r : ℝ ↦ 2 * r)
    apply tsum_congr
    intro v
    by_cases hv : (activeEdges E v).Nonempty ∨ 0 < subsetCount (touchingVertices E e) v
    · simp only [ite_eq_left hv]
    · simp only [ite_eq_right hv]

theorem once_poisson_bound (G : Finset ι) (p : ι → ℝ) (hp : ∀ x ∈ G, 0 ≤ p x)
    (E : Finset (Finset ι)) (hE : ∀ f ∈ E, f ⊆ G ∧ f.card = 2)
    (e : Finset ι) (he : e ∈ E) :
    let U := PositionalBernoulliProducts.poisson G p
    ‖once E (ofFinite (atom (edgeVector e)) * U) - U‖ ≤
      2 * ((∑ f ∈ E, ∏ x ∈ f, p x) + ∑ x ∈ touchingVertices E e, p x) := by
  have hb := PositionalPoissonBadEvents.active_or_subset_bound G (touchingVertices E e)
    (touching_subset E e G (fun f hf ↦ (hE f hf).1)) p hp E hE
  exact (once_bound E e he (fun f hf ↦ (hE f hf).2) _ (poisson_isProbability G p hp).1).trans
    (mul_le_mul_of_nonneg_left hb.2 (by norm_num))

theorem isolated_poisson_bound (G : Finset ι) (p : ι → ℝ) (hp : ∀ x ∈ G, 0 ≤ p x)
    (E : Finset (Finset ι)) (hE : ∀ f ∈ E, f ⊆ G ∧ f.card = 2)
    (e : Finset ι) (he : e ∈ E) :
    let U := PositionalBernoulliProducts.poisson G p
    ‖isolated E (ofFinite (atom (edgeVector e)) * U) - U‖ ≤
      2 * ((∑ f ∈ E, ∏ x ∈ f, p x) + ∑ x ∈ touchingVertices E e, p x) := by
  have hb := PositionalPoissonBadEvents.active_or_subset_bound G (touchingVertices E e)
    (touching_subset E e G (fun f hf ↦ (hE f hf).1)) p hp E hE
  exact (isolated_bound E e he (fun f hf ↦ (hE f hf).2) _ (poisson_isProbability G p hp).1).trans
    (mul_le_mul_of_nonneg_left hb.2 (by norm_num))

end PaperP1.PositionalInsertedPairCoupling
