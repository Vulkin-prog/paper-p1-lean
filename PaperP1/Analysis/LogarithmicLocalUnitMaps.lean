module

public import PaperP1.Analysis.SimplifiedUnitMapGridCount

/-! # Genuine local curve maps with polynomial-logarithmic full-image counts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogarithmicLocalUnitMaps

open MvPolynomial Set TotalDegreeMonomials AffineUnitGraphParametrization
open scoped ContDiff


def HasMap (P : MvPolynomial (Fin 2) ℝ) (k : ℕ) (z : Fin 2 → ℝ) : Prop :=
  ∃ ψ : Fin 2 → ℝ → ℝ,
    (∀ i, ContDiffOn ℝ ∞ (ψ i) (Ioo (0 : ℝ) 1)) ∧
    UnitJets (Fintype.card (Index k) - 1) ψ ∧
    (∃ i : Fin 2, ∃ u c : ℝ, 0 < c ∧ ∀ t ∈ Ioo (0 : ℝ) 1, ψ i t = u + c * t) ∧
    InjOn (fun t ↦ fun i ↦ ψ i t) (Ioo (0 : ℝ) 1) ∧
    (∀ t ∈ Ioo (0 : ℝ) 1, eval (fun i ↦ ψ i t) P = 0) ∧
    (fun i ↦ ψ i (1 / 2)) = z ∧
    ∀ N : ℕ, 0 < N → Real.log (N : ℝ) ≤ k → ∀ S : Finset (Fin 2 → ℝ),
      (∀ w ∈ S, ∃ t ∈ Ioo (0 : ℝ) 1, (fun i ↦ ψ i t) = w) →
      (∀ w ∈ S, ∃ v : Fin 2 → ℤ, ∀ i, w i = (v i : ℝ) / N) →
      (S.card : ℝ) ≤ 32 * Real.exp 4 * ((k + 1 : ℕ) : ℝ) ^ 8

theorem exists_at_nonexceptional (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (k : ℕ) (hk : 1 ≤ k) (hkD : k < P.totalDegree) (z : Fin 2 → ℝ)
    (hzero : eval z P = 0) (hbox : ∀ i, |z i| < 1)
    (hnot : z ∉ JointGraphChebyshevExceptions.points P (Fintype.card (Index k) - 1) k) :
    HasMap P k z := by
  obtain ⟨ψ, hsmooth, hjets, haffine, hinj, hcurve, _havoid, hmid, hpoly⟩ :=
    JointLocalUnitCountingMaps.exists_at_nonexceptional P hP (Fintype.card (Index k) - 1) k hkD z hzero hbox hnot
  refine ⟨ψ, hsmooth, hjets, haffine, hinj, hcurve, hmid, ?_⟩
  intro N hN hlog S hS hgrid
  exact SimplifiedUnitMapGridCount.logarithmic_point_count k hk N hN hlog ψ hsmooth hjets hpoly S hS hgrid

theorem exists_control_set_and_maps (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (k : ℕ) (hk : 1 ≤ k) (hkD : k < P.totalDegree) :
    ∃ E : Finset (Fin 2 → ℝ),
      (∀ z, z ∈ E ↔ z ∈ JointGraphChebyshevExceptions.points P (Fintype.card (Index k) - 1) k) ∧
      E.card ≤ P.totalDegree ^ 2 * (123 * (k + 1) ^ 6) ∧
      ∀ z : Fin 2 → ℝ, eval z P = 0 → (∀ i, |z i| < 1) → z ∉ E → HasMap P k z := by
  obtain ⟨E, hE, hcard⟩ := JointGraphChebyshevExceptions.exists_finset P hP (Fintype.card (Index k) - 1) k hkD
  refine ⟨E, hE, hcard.trans (Nat.mul_le_mul_left _ (MonomialCountingParameters.exceptional_budget k)), ?_⟩
  intro z hzero hbox hnot
  exact exists_at_nonexceptional P hP k hk hkD z hzero hbox (fun hz ↦ hnot ((hE z).mpr hz))

end PaperP1.LogarithmicLocalUnitMaps
