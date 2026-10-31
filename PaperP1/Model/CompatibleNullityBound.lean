module

public import PaperP1.Model.InfiniteJointMoments
public import PaperP1.Affine.CompatibleNullity

/-!
# Article Lemma 4.3 under the actual infinite prime-sign law

The maximum is over positive actual joint masses and the relative nullity of
effective square-class images. Its comparison, equality in compatible families
and the centered-moment bound are all proved, including the empty family.
-/

@[expose] public noncomputable section

open scoped BigOperators
open PaperP1.Arithmetic PaperP1.Affine PaperP1.Algebra PaperP1.Probability

namespace PaperP1.Model.InfiniteStarts

def runRelativeNullity (L : ℕ) (I : Finset ℕ) : ℕ :=
  relativeNullityOn (fun x => squareClassSpace x L) I

def runCompatibleNullity (L : ℕ) (I : Finset ℕ) : ℕ :=
  compatibleNullityOn (fun x => squareClassSpace x L) (infiniteJointMoment L) I

theorem runCompatibleNullity_eq_maximum (L : ℕ) (I : Finset ℕ) :
    runCompatibleNullity L I =
      (I.powerset.filter fun A => 0 < infiniteJointMoment L A).sup (runRelativeNullity L) :=
  compatibleNullityOn_eq_filtered_sup _ _ _

theorem runCompatibleNullity_attained (L : ℕ) (I : Finset ℕ) :
    ∃ A ⊆ I, 0 < infiniteJointMoment L A ∧
      runCompatibleNullity L I = runRelativeNullity L A := by
  have hne : (I.powerset.filter fun A => 0 < infiniteJointMoment L A).Nonempty := by
    refine ⟨∅, ?_⟩
    simp
  obtain ⟨A, hA, heq⟩ := Finset.exists_mem_eq_sup
    (I.powerset.filter fun A => 0 < infiniteJointMoment L A) hne (runRelativeNullity L)
  obtain ⟨hsub, hq⟩ := Finset.mem_filter.mp hA
  exact ⟨A, Finset.mem_powerset.mp hsub, hq, (runCompatibleNullity_eq_maximum L I).trans heq⟩

theorem runRelativeNullity_mono (L : ℕ) {I J : Finset ℕ} (hsub : I ⊆ J) :
    runRelativeNullity L I ≤ runRelativeNullity L J :=
  relativeNullityOn_mono _ hsub

theorem runCompatibleNullity_le_relative (L : ℕ) (I : Finset ℕ) :
    runCompatibleNullity L I ≤ runRelativeNullity L I :=
  compatibleNullityOn_le _ _ _

theorem runCompatibleNullity_eq_of_positive_joint (L : ℕ) (I : Finset ℕ)
    (hq : 0 < infiniteJointMoment L I) :
    runCompatibleNullity L I = runRelativeNullity L I :=
  compatibleNullityOn_eq_of_pos _ _ _ hq

@[simp]
theorem runRelativeNullity_empty (L : ℕ) : runRelativeNullity L ∅ = 0 :=
  relativeNullityOn_empty _

@[simp]
theorem runCompatibleNullity_empty (L : ℕ) : runCompatibleNullity L ∅ = 0 :=
  compatibleNullityOn_empty _ _

theorem infinite_centered_compatible_nullity_bound (L : ℕ) (I : Finset ℕ) (hL : 0 < L)
    (hp : ∀ x ∈ I, 0 < infiniteMarginal x L) :
    |infiniteCenteredCoefficient L I| ≤ (2 ^ I.card : ℝ) *
      (∏ x ∈ I, infiniteMarginal x L) * (2 ^ runCompatibleNullity L I : ℝ) := by
  let M := I.sup fun x => x + L
  have hcut : ∀ x ∈ I, x + L ≤ M := fun x hx => Finset.le_sup (f := fun x => x + L) hx
  rw [infiniteCenteredCoefficient_eq_transform M L I hcut]
  apply centeredCoefficient_compatibleNullity_bound (fun x => squareClassSpace x L)
    (fun x => infiniteMarginal x L) (infiniteJointMoment L) I hp
  · intro A _
    exact infiniteJointMoment_nonneg L A
  · intro A hsub hq
    exact infiniteJointMoment_exact_of_pos M L A hL (fun x hx => hcut x (hsub hx)) hq

/-- Full conclusion of article Lemma 4.3. No arithmetic, nominal marginal or
independent-block premise is assumed. -/
theorem compatible_nullity_majorant (L : ℕ) (I : Finset ℕ) (hL : 0 < L)
    (hp : ∀ x ∈ I, 0 < infiniteMarginal x L) :
    |infiniteCenteredCoefficient L I| ≤ (2 ^ I.card : ℝ) *
      (∏ x ∈ I, infiniteMarginal x L) * (2 ^ runCompatibleNullity L I : ℝ) ∧
    runCompatibleNullity L I ≤ runRelativeNullity L I ∧
    (0 < infiniteJointMoment L I → runCompatibleNullity L I = runRelativeNullity L I) := by
  exact ⟨infinite_centered_compatible_nullity_bound L I hL hp,
    runCompatibleNullity_le_relative L I, runCompatibleNullity_eq_of_positive_joint L I⟩

end PaperP1.Model.InfiniteStarts
