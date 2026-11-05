module

public import PaperP1.Analysis.ShortIntervalGridInterpolation
public import PaperP1.Analysis.JointLocalUnitCountingMaps

/-! # Actual short-interval grid populations on the constructed local curve maps

The polynomial is obtained from actual vanishing grid minors. The previously
proved strict all-polynomial zero count then bounds the original point set.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShortIntervalGridPointCount

open MvPolynomial Set TotalDegreeMonomials AffineUnitGraphParametrization GridCurveMinorVanishing
open scoped ContDiff

theorem point_count (k : ℕ) (hk : 1 ≤ k) (N : ℕ) (hN : 0 < N)
    (ψ : Fin 2 → ℝ → ℝ) (hψ : ∀ i, ContDiffOn ℝ ∞ (ψ i) (Ioo (0 : ℝ) 1))
    (hjet : UnitJets (Fintype.card (Index k) - 1) ψ)
    (hpoly : ∀ Q : MvPolynomial (Fin 2) ℝ, Q ≠ 0 → Q.totalDegree ≤ k →
      ∀ S : Finset (Fin 2 → ℝ),
        (∀ w ∈ S, (∃ t ∈ Ioo (0 : ℝ) 1, (fun i ↦ ψ i t) = w) ∧ eval w Q = 0) →
          S.card < Fintype.card (Index k))
    (c δ : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hsmall : (N : ℝ) ^ (k * Fintype.card (Index k)) * analyticBudget (Fintype.card (Index k)) k δ < 1)
    (S : Finset (Fin 2 → ℝ))
    (hS : ∀ w ∈ S, ∃ t ∈ Ioo (0 : ℝ) 1, |t - c| ≤ δ ∧ (fun i ↦ ψ i t) = w)
    (hgrid : ∀ w ∈ S, ∃ z : Fin 2 → ℤ, ∀ i, w i = (z i : ℝ) / N) :
    S.card < Fintype.card (Index k) := by
  classical
  choose x hx hd he using fun w : S ↦ hS w.val w.property
  choose z hz using fun w : S ↦ hgrid w.val w.property
  have hactual : ∀ w : S, ∀ i, ψ i (x w) = (z w i : ℝ) / N := by
    intro w i
    rw [congrFun (he w) i]
    exact hz w i
  obtain ⟨Q, hQ, hdegree, hzero⟩ := ShortIntervalGridInterpolation.exists_polynomial k hk N hN
    ψ hψ hjet c δ hc hδ hδone x hx hd z hactual hsmall
  apply hpoly Q hQ hdegree S
  intro w hw
  let v : S := ⟨w, hw⟩
  refine ⟨⟨x v, hx v, he v⟩, ?_⟩
  have hh := hzero v
  rw [he v] at hh
  exact hh

theorem exists_local_counting_map (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (k : ℕ) (hk : 1 ≤ k) (hkD : k < P.totalDegree) (z : Fin 2 → ℝ)
    (hzero : eval z P = 0) (hbox : ∀ i, |z i| < 1)
    (hnot : z ∉ JointGraphChebyshevExceptions.points P (Fintype.card (Index k) - 1) k) :
    ∃ ψ : Fin 2 → ℝ → ℝ,
      (∀ i, ContDiffOn ℝ ∞ (ψ i) (Ioo (0 : ℝ) 1)) ∧
      UnitJets (Fintype.card (Index k) - 1) ψ ∧
      (∃ i : Fin 2, ∃ u c : ℝ, 0 < c ∧ ∀ t ∈ Ioo (0 : ℝ) 1, ψ i t = u + c * t) ∧
      InjOn (fun t ↦ fun i ↦ ψ i t) (Ioo (0 : ℝ) 1) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, eval (fun i ↦ ψ i t) P = 0) ∧
      (fun i ↦ ψ i (1 / 2)) = z ∧
      ∀ N : ℕ, 0 < N → ∀ c δ : ℝ, c ∈ Ioo (0 : ℝ) 1 → 0 ≤ δ → δ ≤ 1 →
        (N : ℝ) ^ (k * Fintype.card (Index k)) * analyticBudget (Fintype.card (Index k)) k δ < 1 →
        ∀ S : Finset (Fin 2 → ℝ),
          (∀ w ∈ S, ∃ t ∈ Ioo (0 : ℝ) 1, |t - c| ≤ δ ∧ (fun i ↦ ψ i t) = w) →
          (∀ w ∈ S, ∃ v : Fin 2 → ℤ, ∀ i, w i = (v i : ℝ) / N) →
          S.card < Fintype.card (Index k) := by
  obtain ⟨ψ, hsmooth, hjets, haffine, hinj, hcurve, _havoid, hmid, hpoly⟩ :=
    JointLocalUnitCountingMaps.exists_at_nonexceptional P hP (Fintype.card (Index k) - 1) k hkD z hzero hbox hnot
  refine ⟨ψ, hsmooth, hjets, haffine, hinj, hcurve, hmid, ?_⟩
  intro N hN c δ hc hδ hδone hsmall S hS hgrid
  exact point_count k hk N hN ψ hsmooth hjets hpoly c δ hc hδ hδone hsmall S hS hgrid

end PaperP1.ShortIntervalGridPointCount
