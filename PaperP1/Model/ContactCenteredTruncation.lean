module

public import PaperP1.Model.ContactFamilySeeds
public import PaperP1.Model.ShiftedCountMoments
public import PaperP1.Probability.SeededCenteredTruncation
public import PaperP1.Model.CompatibleActivitySplit

/-! # The actual centered contact mass reduces to a seed kernel and one higher shifted moment -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ContactCenteredTruncation

open Finset PaperP1.Algebra PaperP1.Probability PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.HeterogeneousDirectMaximum

def families (G : Finset ℕ) (L r : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (G.powersetCard r).filter (fun I ↦ ∃ e ∈ ClosePairs.pairs G L, e ⊆ I)

def seedKernel (G : Finset ℕ) (L : ℕ) : ℝ :=
  ∑ e ∈ ClosePairs.pairs G L, (infiniteJointMoment L e + 3 * ∏ x ∈ e, infiniteMarginal x L)

theorem mem_families (G : Finset ℕ) (L r : ℕ) (I : Finset ℕ) :
    I ∈ families G L r ↔ I ⊆ G ∧ I.card = r ∧
      ∃ x ∈ I, ∃ y ∈ I, x < y ∧ y ≤ x + L := by
  classical
  constructor
  · intro hI
    obtain ⟨hI, e, he, heI⟩ := mem_filter.mp hI
    obtain ⟨x, y, _hxG, _hyG, hxy, hyL, hpair⟩ := ClosePairs.data G L e he
    exact ⟨(mem_powersetCard.mp hI).1, (mem_powersetCard.mp hI).2,
      x, heI (by rw [hpair]; simp), y, heI (by rw [hpair]; simp), hxy, hyL⟩
  · rintro ⟨hIG, hcard, x, hx, y, hy, hxy, hyL⟩
    apply mem_filter.mpr
    refine ⟨mem_powersetCard.mpr ⟨hIG, hcard⟩, {x, y}, ?_, ?_⟩
    · exact mem_filter.mpr ⟨mem_powersetCard.mpr
        ⟨by intro z hz; simp only [mem_insert, mem_singleton] at hz
            rcases hz with rfl | rfl <;> apply hIG <;> assumption,
          by simp [ne_of_lt hxy]⟩,
        x, mem_insert_self _ _, y, mem_insert_of_mem (mem_singleton_self _), hxy, hyL⟩
    · intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption

theorem seedKernel_nonneg (G : Finset ℕ) (L : ℕ) : 0 ≤ seedKernel G L :=
  sum_nonneg fun e _ ↦ add_nonneg (infiniteJointMoment_nonneg L e)
    (mul_nonneg (by norm_num) (prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L))

theorem finite_bound {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N)
    (r : ℕ) (hr : 2 ≤ r) (R : ℝ) (hR : 0 < R) (m : ℕ) (hm : r ≤ m) :
    CompatibleActivitySplit.absolute L (families G L r) ≤ R ^ (r - 2) * seedKernel G L +
      ShiftedCountMoments.moment G L m / R ^ (m - r) := by
  classical
  let M := dyadicCutoff N L
  let P := cylinderProbability M
  let J : ℕ → SampleSpace M → Bool := fun x ↦ startIndicator x L
  let p := fun x ↦ infiniteMarginal x L
  have hcut := CountObservables.dyadic_subset_cutoff (L := L) hG
  have hmean : ∀ x ∈ G, exactMarginal P J x = p x := by
    intro x hx
    exact (infiniteMarginal_eq_finite (hcut x hx)).symm
  have hF : ∀ e ∈ ClosePairs.pairs G L, e ⊆ G ∧ e.card = 2 := by
    intro e he
    exact mem_powersetCard.mp (ClosePairs.subset G L he)
  have hT : ∀ I ∈ families G L r, I ⊆ G ∧ I.card = r ∧ ∃ e ∈ ClosePairs.pairs G L, e ⊆ I := by
    intro I hI
    obtain ⟨hIG, hseed⟩ := mem_filter.mp hI
    exact ⟨(mem_powersetCard.mp hIG).1, (mem_powersetCard.mp hIG).2, hseed⟩
  have hfinite := SeededCenteredTruncation.finite_bound P J p
    (fun x ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L) G hmean r hr
    (ClosePairs.pairs G L) (families G L r) hF hT R hR m hm
  have hleft : CompatibleActivitySplit.absolute L (families G L r) =
      ∑ I ∈ families G L r, |centeredMoment P.weight (fun x ω ↦ (indicatorValue (J x ω) : ℝ)) p I| := by
    apply sum_congr rfl
    intro I hI
    rw [CompressedJointMoments.centered_to_finite M L I (fun x hx ↦ hcut x ((hT I hI).1 hx))]
  have hseed : (∑ e ∈ ClosePairs.pairs G L, (finiteJointMoment P J e + 3 * ∏ x ∈ e, p x)) =
      seedKernel G L := by
    apply sum_congr rfl
    intro e he
    rw [infiniteJointMoment_eq_finite M L e (fun x hx ↦ hcut x ((hF e he).1 hx))]
  have htotal (σ : SampleSpace M) :
      (∑ x ∈ G, ((indicatorValue (J x σ) : ℝ) + p x)) =
        (indicatorCount G J σ : ℝ) + actualMean G L := by
    have hind (b : Bool) : (b.toNat : ℝ) = indicatorValue b := by cases b <;> simp [indicatorValue]
    simp only [sum_add_distrib, indicatorCount, Nat.cast_sum, hind]
    rfl
  have hmoment : finiteExpectation P.weight (fun σ ↦
      (∑ x ∈ G, ((indicatorValue (J x σ) : ℝ) + p x)) ^ m) = ShiftedCountMoments.moment G L m := by
    rw [ShiftedCountMoments.eq_finite hG]
    congr 1
    funext σ
    rw [htotal σ]
  rw [hseed, hmoment] at hfinite
  rw [hleft]
  exact hfinite

end PaperP1.ContactCenteredTruncation
