module

public import PaperP1.Algebra.MomentReconstruction
public import PaperP1.Affine.CompressedRelationSupport
public import PaperP1.Model.CanonicalRunComponents
public import PaperP1.Model.InfiniteTripleCancellation
public import PaperP1.Model.RetainedGoodEdges
public import PaperP1.Model.SquareClassFourier

/-! # Exact heterogeneous joint moments of direct and pair-compressed actual families -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompressedJointMoments

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Algebra PaperP1.Probability PaperP1.Model
  PaperP1.Model.InfiniteStarts PaperP1.MomentReconstruction PaperP1.CompressedRelationSupport

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem centered_to_finite (M L : ℕ) (I : Finset ℕ) (hcut : ∀ x ∈ I, x + L ≤ M) :
    infiniteCenteredCoefficient L I = centeredMoment (cylinderProbability M).weight
      (fun x ω ↦ (indicatorValue (startIndicator x L ω) : ℝ)) (fun x ↦ infiniteMarginal x L) I := by
  rw [infiniteCenteredCoefficient_eq_transform M L I hcut, centeredMoment_eq_centeredCoefficient]
  unfold centeredCoefficient
  apply sum_congr rfl
  intro A hA
  rw [infiniteJointMoment_eq_finite M L A (fun x hx ↦ hcut x (mem_powerset.mp hA hx))]
  rfl

theorem infinite_uncentered_expansion (L : ℕ) (I : Finset ℕ) :
    infiniteJointMoment L I = ∑ A ∈ I.powerset,
      infiniteCenteredCoefficient L A * ∏ x ∈ I \ A, infiniteMarginal x L := by
  let M := I.sup (fun x ↦ x + L)
  have hcut (x : ℕ) (hx : x ∈ I) : x + L ≤ M := le_sup (f := fun x ↦ x + L) hx
  have h := finite_uncentered_expansion (cylinderProbability M).weight
    (fun x ω ↦ (indicatorValue (startIndicator x L ω) : ℝ)) (fun x ↦ infiniteMarginal x L) I
  change finiteJointMoment (cylinderProbability M) (fun x ↦ startIndicator x L) I = _ at h
  rw [← infiniteJointMoment_eq_finite M L I hcut] at h
  rw [h]
  apply sum_congr rfl
  intro A hA
  rw [centered_to_finite M L A (fun x hx ↦ hcut x (mem_powerset.mp hA hx))]

theorem centered_empty (L : ℕ) : infiniteCenteredCoefficient L ∅ = 1 := by
  simp [infiniteCenteredCoefficient]

theorem centered_pair (L : ℕ) (e : Finset ℕ) (he : e.card = 2) :
    infiniteCenteredCoefficient L e = infiniteJointMoment L e - ∏ x ∈ e, infiniteMarginal x L := by
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp he
  rw [InfiniteTripleCancellation.coefficient_eq_transform,
    centeredCoefficient_pair_eq_covariance _ _ hxy (infiniteJointMoment_empty L)
      (InfiniteTripleCancellation.singleton_joint L x) (InfiniteTripleCancellation.singleton_joint L y),
    prod_pair hxy]

theorem centered_zero_of_no_full_support (L : ℕ) (hL : 0 < L) (I : Finset ℕ)
    (hp : ∀ x ∈ I, 0 < infiniteMarginal x L)
    (hno : ¬ ∃ w, IsFullSupportRelation (fun i : I ↦ squareClassSpace i.val L) w) :
    infiniteCenteredCoefficient L I = 0 := by
  by_contra hn
  have hcut (x : I) : x.val + L ≤ I.sup (fun x ↦ x + L) := le_sup (f := fun x ↦ x + L) x.property
  have hfamily : infiniteFamilyCenteredMoment L (fun x : I ↦ x.val) ≠ 0 := by
    rwa [← infiniteCenteredCoefficient_eq_family_subtype]
  exact hno (squareClass_full_relation_of_ne_zero (I.sup (fun x ↦ x + L)) L (fun x : I ↦ x.val)
    hL hcut (fun x ↦ hp x.val x.property) hfamily)

theorem direct_joint_factor (L : ℕ) (hL : 0 < L) (I : Finset ℕ)
    (hp : ∀ x ∈ I, 0 < infiniteMarginal x L)
    (hzero : relativeNullityOn (fun x ↦ squareClassSpace x L) I = 0) :
    infiniteJointMoment L I = ∏ x ∈ I, infiniteMarginal x L := by
  rw [infinite_uncentered_expansion]
  calc
    _ = infiniteCenteredCoefficient L ∅ * ∏ x ∈ I \ ∅, infiniteMarginal x L := by
      apply sum_eq_single ∅
      · intro A hA hne
        have hAI := mem_powerset.mp hA
        have hmono := relativeNullityOn_mono (fun x ↦ squareClassSpace x L) hAI
        rw [hzero] at hmono
        have hAzero : relativeNullityOn (fun x ↦ squareClassSpace x L) A = 0 := by omega
        rw [centered_zero_of_no_full_support L hL A (fun x hx ↦ hp x (hAI hx))
          (no_full_support_of_nullity_zero _ A (nonempty_iff_ne_empty.mpr hne) hAzero), zero_mul]
      · simp
    _ = _ := by rw [centered_empty, sdiff_empty, one_mul]

theorem compressed_joint_factor (L : ℕ) (hL : 0 < L) (e I : Finset ℕ) (he : e.card = 2)
    (hp : ∀ x ∈ I, 0 < infiniteMarginal x L)
    (hcomp : RetainedDependence.Compressed (fun x ↦ squareClassSpace x L) e I) :
    infiniteJointMoment L I = infiniteJointMoment L e * ∏ x ∈ I \ e, infiniteMarginal x L := by
  classical
  let f : Finset ℕ → ℝ := fun A ↦ infiniteCenteredCoefficient L A * ∏ x ∈ I \ A, infiniteMarginal x L
  have hsmall : ({∅, e} : Finset (Finset ℕ)) ⊆ I.powerset := by
    intro A hA
    obtain rfl | hA := mem_insert.mp hA
    · exact mem_powerset.mpr (empty_subset I)
    · exact mem_powerset.mpr (mem_singleton.mp hA ▸ hcomp.1)
  have hsum : (∑ A ∈ I.powerset, f A) = ∑ A ∈ ({∅, e} : Finset (Finset ℕ)), f A := by
    symm
    apply sum_subset hsmall
    intro A hA hnot
    have hAI := mem_powerset.mp hA
    have hne : A ≠ ∅ := by intro h; exact hnot (by simp [h])
    have hnePair : A ≠ e := by intro h; exact hnot (by simp [h])
    have hz := centered_zero_of_no_full_support L hL A (fun x hx ↦ hp x (hAI hx))
      (no_full_support_restriction_except_pair _ e I he hcomp A hAI
        (nonempty_iff_ne_empty.mpr hne) hnePair)
    dsimp [f]
    rw [hz, zero_mul]
  have heEmpty : (∅ : Finset ℕ) ≠ e := by intro h; rw [← h] at he; simp at he
  have hprod : (∏ x ∈ I \ e, infiniteMarginal x L) * (∏ x ∈ e, infiniteMarginal x L) =
      ∏ x ∈ I, infiniteMarginal x L := prod_sdiff hcomp.1
  rw [infinite_uncentered_expansion]
  change (∑ A ∈ I.powerset, f A) = _
  rw [hsum, sum_pair heEmpty]
  dsimp [f]
  rw [centered_empty, sdiff_empty, one_mul, centered_pair L e he]
  nlinarith only [hprod]

theorem regular_direct_joint {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (I : Finset ℕ)
    (hreg : I ⊆ RegularStarts.regularStarts N L)
    (hzero : relativeNullityOn (fun x ↦ squareClassSpace x L) I = 0) :
    infiniteJointMoment L I = ((2 ^ L : ℝ)⁻¹) ^ I.card := by
  have hm (x : ℕ) (hx : x ∈ I) : infiniteMarginal x L = (2 ^ L : ℝ)⁻¹ := by
    have hxN := (mem_Ico.mp (RegularStarts.mem_regularStarts.mp (hreg hx)).1).1
    exact RegularStarts.marginal_on_regular (by omega) hL (hreg hx)
  rw [direct_joint_factor L hL I (fun x hx ↦ by rw [hm x hx]; positivity) hzero]
  calc
    _ = ∏ _x ∈ I, (2 ^ L : ℝ)⁻¹ := prod_congr rfl hm
    _ = _ := by simp

theorem regular_compressed_joint {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (e I : Finset ℕ)
    (he : e.card = 2) (hreg : I ⊆ RegularStarts.regularStarts N L)
    (hcomp : RetainedDependence.Compressed (fun x ↦ squareClassSpace x L) e I) :
    infiniteJointMoment L I = infiniteJointMoment L e * ((2 ^ L : ℝ)⁻¹) ^ (I.card - 2) := by
  have hm (x : ℕ) (hx : x ∈ I) : infiniteMarginal x L = (2 ^ L : ℝ)⁻¹ := by
    have hxN := (mem_Ico.mp (RegularStarts.mem_regularStarts.mp (hreg hx)).1).1
    exact RegularStarts.marginal_on_regular (by omega) hL (hreg hx)
  rw [compressed_joint_factor L hL e I he (fun x hx ↦ by rw [hm x hx]; positivity) hcomp]
  have hprod : (∏ x ∈ I \ e, infiniteMarginal x L) = ((2 ^ L : ℝ)⁻¹) ^ (I \ e).card := by
    calc
      _ = ∏ _x ∈ I \ e, (2 ^ L : ℝ)⁻¹ := prod_congr rfl (fun x hx ↦ hm x (mem_sdiff.mp hx).1)
      _ = _ := by simp
  rw [hprod, card_sdiff_of_subset hcomp.1, he]

end PaperP1.CompressedJointMoments
