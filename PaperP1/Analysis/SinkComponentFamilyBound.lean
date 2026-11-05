module

public import PaperP1.Algebra.CurveComponentBarrier
public import PaperP1.Analysis.ConnectedBarrierCrossing
public import PaperP1.Analysis.PolynomialVelocitySmooth

/-! # A quadratic bound for disjoint connected curve populations approaching barrier zeros -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SinkComponentFamilyBound

open MvPolynomial Set CurveComponentBarrier

theorem card_bound {ι : Type*} (I : Finset ι) (P : MvPolynomial (Fin 2) ℝ)
    (hP : Irreducible P) (C : ι → Set (Fin 2 → ℝ))
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (C i) (C j))
    (hconn : ∀ i ∈ I, IsPreconnected (C i))
    (hcurve : ∀ i ∈ I, ∀ z ∈ C i, eval z P = 0)
    (a w : ι → Fin 2 → ℝ) (ha : ∀ i ∈ I, a i ∈ C i)
    (hpos : ∀ i ∈ I, 0 < eval (a i) (barrier P))
    (hw : ∀ i ∈ I, w i ∈ closure (C i))
    (hwP : ∀ i ∈ I, eval (w i) P = 0)
    (hwH : ∀ i ∈ I, eval (w i) (barrier P) = 0) :
    I.card ≤ P.totalDegree * (2 * P.totalDegree + 4) := by
  classical
  by_cases hI : I.Nonempty
  · obtain ⟨ε, hε, hεa⟩ := ConnectedBarrierCrossing.common_positive_level I
      (fun i ↦ eval (a i) (barrier P)) hpos
    have hcont : Continuous (fun z : Fin 2 → ℝ ↦ eval z (barrier P)) :=
      (PolynomialVelocitySmooth.contDiff_eval (barrier P) 0).continuous
    have hcross (i : I) : ∃ z ∈ C i, eval z (barrier P) = ε :=
      ConnectedBarrierCrossing.crossing _ hcont _ (hconn i i.property) _ (ha i i.property)
        _ (hw i i.property) (hwH i i.property) ε hε (hεa i i.property)
    choose z hzC hzH using hcross
    have hinj : Function.Injective z := by
      intro i j hij
      apply Subtype.ext
      by_contra hne
      exact Set.disjoint_left.mp (hdisj i i.property j j.property hne)
        (hzC i) (hij ▸ hzC j)
    obtain ⟨i₀, hi₀⟩ := hI
    have hc := level_population_card P hP (w i₀) (hwP i₀ hi₀) (hwH i₀ hi₀)
      ε hε.ne' (Finset.univ.image z) (by
        intro v hv
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
        exact ⟨hcurve i i.property _ (hzC i), hzH i⟩)
    simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe] using hc
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hI, Finset.card_empty, Nat.zero_le]

end PaperP1.SinkComponentFamilyBound
