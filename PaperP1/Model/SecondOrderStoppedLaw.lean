module

public import PaperP1.Model.SecondOrderPositiveMass
public import PaperP1.Model.RetainedStoppedLaw

/-! # A finite all-pair reconstruction bound on the original full heterogeneous count law -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SecondOrderStoppedLaw

open Finset MeasureTheory PaperP1.Arithmetic PaperP1.Affine PaperP1.Algebra PaperP1.Probability
  PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.SecondOrderRetainedClass PaperP1.SecondOrderRetainedReference

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def small (G : Finset ℕ) (L K : ℕ) : Finset (Finset ℕ) :=
  (boundarySets G (Retained G L)).filter fun I ↦ I.card ≤ K

def large (G : Finset ℕ) (L K : ℕ) : Finset (Finset ℕ) :=
  (boundarySets G (Retained G L)).filter fun I ↦ K < I.card

def largeMass (G : Finset ℕ) (L K : ℕ) : ℝ :=
  ∑ I ∈ large G L K, (2 : ℝ) ^ I.card * infiniteJointMoment L I

theorem finite_count_bound (G : Finset ℕ) (L : ℕ) :
    SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure
      (FiniteLawEmbedding.embed (retainedReference G L)) ≤
      ∑ I ∈ boundarySets G (Retained G L), (2 : ℝ) ^ I.card * infiniteJointMoment L I := by
  let M := MaximumDirectActive.cutoff G L
  let J : ℕ → SampleSpace M → Bool := fun x ↦ startIndicator x L
  have hcut (x : ℕ) (hx : x ∈ G) : x + L ≤ M := le_sup (f := fun x ↦ x + L) hx
  have href : retainedCountReference G (Retained G L) (cylinderProbability M) J = retainedReference G L := by
    apply sum_congr rfl
    intro I hI
    have hIG := mem_powerset.mp (mem_filter.mp hI).1
    rw [← infiniteJointMoment_eq_finite M L I (fun x hx ↦ hcut x (hIG hx))]
  have hstop := stopped_finite_count_l1_bound G (Retained G L) (cylinderProbability M) J (hereditary G L) (empty G L)
  rw [href] at hstop
  have hlaw : (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure =
      FiniteLawEmbedding.embed (countLaw G (cylinderProbability M).weight J) := by
    rw [← OriginalCountLawCoupling.finite_law M L G hcut]
    exact RetainedStoppedLaw.finite_law_embedding G (cylinderProbability M) J
  rw [hlaw, SignedAtomicDistance.finite_eq]
  apply hstop.trans_eq
  apply sum_congr rfl
  intro I hI
  have hIG := mem_powerset.mp (mem_filter.mp hI).1
  rw [← infiniteJointMoment_eq_finite M L I (fun x hx ↦ hcut x (hIG hx))]

theorem small_bound {N L : ℕ} (hN : 0 < N) (G : Finset ℕ) (hG : G ⊆ dyadicBlock N)
    (hL : 0 < L) (K : ℕ) :
    (∑ I ∈ small G L K, (2 : ℝ) ^ I.card * infiniteJointMoment L I) ≤
      Real.exp (∑ x ∈ G, 2 * infiniteMarginal x L) *
        (∑ D ∈ SecondOrderIndependentDeficit.primitives G L, ActualComponentRemainder.weight L 2 D) +
      8 * AllPairExtensionDeficit.deficit G L 2 +
      Real.exp (∑ x ∈ G, 2 * infiniteMarginal x L) *
        (Real.exp ((∑ e ∈ G.powersetCard 2, ActualComponentRemainder.weight L 2 e) +
          ∑ C ∈ ActualComponentRemainder.higher G L K 2, ActualComponentRemainder.weight L 2 C) -
          1 - ∑ e ∈ G.powersetCard 2, ActualComponentRemainder.weight L 2 e) := by
  have hF : ∀ I ∈ small G L K, I ⊆ G ∧ I.Nonempty ∧ I.card ≤ K ∧
      (runRelativeNullity L I : ℝ) ≤ 2 * L ∧ ¬Retained G L I := by
    intro I hI
    obtain ⟨hIB, hsize⟩ := mem_filter.mp hI
    obtain ⟨hIG, hboundary⟩ := mem_filter.mp hIB
    have hsub := mem_powerset.mp hIG
    refine ⟨hsub, orderedBoundary_nonempty (empty G L) hboundary, hsize, ?_, hboundary.1⟩
    exact_mod_cast (boundary_nullity hN G I hG hsub hboundary).2
  simpa only [show (2 : ℝ) * 2 ^ 2 = 8 by norm_num] using
    SecondOrderPositiveMass.finite_bound G L K hL 2 2 (by norm_num) (small G L K) hF

theorem finite_bound {N L : ℕ} (hN : 0 < N) (G : Finset ℕ) (hG : G ⊆ dyadicBlock N)
    (hL : 0 < L) (K : ℕ) :
    SignedAtomicDistance.distance (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure
      (FiniteLawEmbedding.embed (pairReference G L)) ≤
      2 * Real.exp (∑ x ∈ G, 2 * infiniteMarginal x L) *
        (∑ D ∈ SecondOrderIndependentDeficit.primitives G L, ActualComponentRemainder.weight L 2 D) +
      16 * AllPairExtensionDeficit.deficit G L 2 +
      Real.exp (∑ x ∈ G, 2 * infiniteMarginal x L) *
        (Real.exp ((∑ e ∈ G.powersetCard 2, ActualComponentRemainder.weight L 2 e) +
          ∑ C ∈ ActualComponentRemainder.higher G L K 2, ActualComponentRemainder.weight L 2 C) -
          1 - ∑ e ∈ G.powersetCard 2, ActualComponentRemainder.weight L 2 e) + largeMass G L K := by
  have hsplit := sum_filter_add_sum_filter_not (boundarySets G (Retained G L)) (fun I ↦ I.card ≤ K)
    (fun I ↦ (2 : ℝ) ^ I.card * infiniteJointMoment L I)
  simp only [not_le] at hsplit
  have hsmall := small_bound hN G hG hL K
  have hfinite := finite_count_bound G L
  have href := retained_error G L hL
  rw [← SignedAtomicDistance.finite_eq] at href
  have htri := SignedAtomicDistance.triangle (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure
    (FiniteLawEmbedding.embed (retainedReference G L)) (FiniteLawEmbedding.embed (pairReference G L))
  change (∑ I ∈ small G L K, (2 : ℝ) ^ I.card * infiniteJointMoment L I) + largeMass G L K = _ at hsplit
  linarith only [hsmall, hfinite, href, htri, hsplit]

end PaperP1.SecondOrderStoppedLaw
