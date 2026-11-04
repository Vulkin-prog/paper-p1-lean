module

public import PaperP1.Model.FiniteDeletedIntensity

/-! # The literal original deleted intensities and their positive two-edge error -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OriginalDeletedIntensity

open Finset PaperP1.Algebra PaperP1.Probability PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PositionalFiniteLaw PaperP1.PositionalDeletedFields PaperP1.PositionalFactorialCovariance

theorem finite_bounds (G : Finset ℕ) (L : ℕ) (E : Finset (Finset ℕ)) (b : ℕ → ℝ)
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) :
    let R := (∑ x ∈ G, |infiniteMarginal x L - b x|) +
      ∑ p ∈ ActiveFamilySecondMoment.ordered E, infiniteJointMoment L (p.1 ∪ p.2)
    (∑ x ∈ G, |mean (onceLaw E G L) x -
      (b x - PositionalCompoundPoisson.incidence E (infiniteJointMoment L) x)|) ≤ R ∧
    (∑ x ∈ G, |mean (isolatedLaw E G L) x -
      (b x - PositionalCompoundPoisson.incidence E (infiniteJointMoment L) x)|) ≤ R := by
  let M := G.sup (fun x ↦ x + L)
  let P := cylinderProbability M
  let J := fun x ↦ startIndicator (M := M) x L
  have hcut (x : ℕ) (hx : x ∈ G) : x + L ≤ M := le_sup (f := fun x ↦ x + L) hx
  have hinc (x : ℕ) : PositionalCompoundPoisson.incidence E (finiteJointMoment P J) x =
      PositionalCompoundPoisson.incidence E (infiniteJointMoment L) x := by
    unfold PositionalCompoundPoisson.incidence
    apply sum_congr rfl
    intro e he
    by_cases hx : x ∈ e
    · simp only [ite_eq_left hx]
      exact (infiniteJointMoment_eq_finite M L e (fun x hx ↦ hcut x ((hE e he).1 hx))).symm
    · simp only [ite_eq_right hx]
  have hbias : (∑ x ∈ G, |exactMarginal P J x - b x|) =
      ∑ x ∈ G, |infiniteMarginal x L - b x| := by
    apply sum_congr rfl
    intro x hx
    rw [← infiniteMarginal_eq_finite (hcut x hx)]
  have hsecond : finiteExpectation P.weight (fun ω ↦
      ((PositionalPairDeletion.activeEdges E (configuration G J ω)).card : ℝ) *
        (((PositionalPairDeletion.activeEdges E (configuration G J ω)).card : ℝ) - 1)) =
      ∑ p ∈ ActiveFamilySecondMoment.ordered E, infiniteJointMoment L (p.1 ∪ p.2) := by
    rw [FiniteDeletedIntensity.finite_factorial_eq P G J E (fun e he ↦ (hE e he).1)]
    apply sum_congr (by congr!)
    intro p hp
    obtain ⟨he, hf⟩ := mem_product.mp (mem_filter.mp hp).1
    have hcutU : ∀ x ∈ p.1 ∪ p.2, x + L ≤ M := fun x hx ↦
      hcut x (union_subset (hE p.1 he).1 (hE p.2 hf).1 hx)
    convert (infiniteJointMoment_eq_finite M L (p.1 ∪ p.2) hcutU).symm using 1
    congr!
  have hOnce := FiniteDeletedIntensity.once_bound P G J E b hE
  have hIsolated := FiniteDeletedIntensity.isolated_bound P G J E b hE
  rw [hbias, hsecond] at hOnce hIsolated
  simp only [hinc] at hOnce hIsolated
  exact ⟨hOnce, hIsolated⟩

end PaperP1.OriginalDeletedIntensity
