module

public import PaperP1.Analysis.SecondRegularComponentFamilyBound
public import PaperP1.Topology.FiniteComponentRepresentatives
public import PaperP1.Combinatorics.FiniteCoverCount

/-! # Actual component representatives and full finite-population grid counts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RegularComponentPopulationAssembly

open MvPolynomial Set JointExceptionalComponentGridCount

theorem first_count (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (E : Finset (Fin 2 → ℝ)) (k : ℕ) (hk : 1 ≤ k)
    (havoid : ∀ z ∈ RegularCurveComponentGraphs.region P (openRegion E),
      z ∉ GraphControlExceptions.points P ((Fintype.card (TotalDegreeMonomials.Index k) - 1) + 1))
    (hWr : ∀ z ∈ RegularCurveComponentGraphs.region P (openRegion E),
      z ∉ MonomialWronskianExceptions.exceptionalPoints P k)
    (N : ℕ) (hN : 0 < N) (hlog : Real.log (N : ℝ) ≤ k)
    (S : Finset (Fin 2 → ℝ))
    (hS : ∀ z ∈ S, z ∈ RegularCurveComponentGraphs.region P (openRegion E))
    (hinit : ∀ z ∈ S, |eval z (pderiv 0 P)| ≤ |eval z (pderiv 1 P)|)
    (hgrid : ∀ w ∈ S, ∃ z : Fin 2 → ℤ, ∀ i, w i = (z i : ℝ) / N) :
    (S.card : ℝ) ≤ ((E.card + P.totalDegree * (2 * P.totalDegree + 4) : ℕ) : ℝ) *
      (2 + 1024 * Real.exp 4 * ((Nat.log2 (2 * N) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 10) := by
  classical
  let F := RegularCurveComponentGraphs.region P (openRegion E)
  obtain ⟨I, hIS, hdisj, hcover⟩ := FiniteComponentRepresentatives.exists_representatives F S hS
  have hI := FirstRegularComponentFamilyBound.card_bound I P hP E id (fun a ha ↦ hS a (hIS ha))
    ((Fintype.card (TotalDegreeMonomials.Index k) - 1) + 1) havoid
    (fun a ha ↦ hinit a (hIS ha)) hdisj
  let A : ℝ := 2 + 1024 * Real.exp 4 * ((Nat.log2 (2 * N) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 10
  let T := fun a ↦ S.filter (fun z ↦ z ∈ connectedComponentIn F a)
  have hT (a : Fin 2 → ℝ) (ha : a ∈ I) : ((T a).card : ℝ) ≤ A := by
    apply RegularComponentUnitGridCount.point_count P (openRegion E) (openRegion_isOpen E) a
      (hS a (hIS ha)) k hk
      (fun z hz ↦ havoid z (connectedComponentIn_subset F a hz))
      (fun z hz ↦ hWr z (connectedComponentIn_subset F a hz))
      (hinit a (hIS ha)) N hN hlog (T a)
      (fun _ hz ↦ (Finset.mem_filter.mp hz).2)
      (fun z hz i ↦ ((hS z (Finset.mem_filter.mp hz).1).2.1 i).le)
      (fun z hz ↦ hgrid z (Finset.mem_filter.mp hz).1)
  have hc := FiniteCoverCount.cardinal_le S I T A (by
    intro z hz
    obtain ⟨a, ha, hza⟩ := hcover z hz
    exact ⟨a, ha, Finset.mem_filter.mpr ⟨hz, hza⟩⟩) hT
  exact hc.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hI) (by dsimp [A]; positivity))

theorem second_count (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (E : Finset (Fin 2 → ℝ)) (k : ℕ) (hk : 1 ≤ k)
    (havoid : ∀ z ∈ SecondRegularCurveComponentGraphs.region P (openRegion E),
      z ∉ GraphControlExceptions.points P ((Fintype.card (TotalDegreeMonomials.Index k) - 1) + 1))
    (hWr : ∀ z ∈ SecondRegularCurveComponentGraphs.region P (openRegion E),
      z ∉ MonomialWronskianExceptions.exceptionalPoints P k)
    (N : ℕ) (hN : 0 < N) (hlog : Real.log (N : ℝ) ≤ k)
    (S : Finset (Fin 2 → ℝ))
    (hS : ∀ z ∈ S, z ∈ SecondRegularCurveComponentGraphs.region P (openRegion E))
    (hinit : ∀ z ∈ S, |eval z (pderiv 1 P)| ≤ |eval z (pderiv 0 P)|)
    (hgrid : ∀ w ∈ S, ∃ z : Fin 2 → ℤ, ∀ i, w i = (z i : ℝ) / N) :
    (S.card : ℝ) ≤ ((E.card + P.totalDegree * (2 * P.totalDegree + 4) : ℕ) : ℝ) *
      (2 + 1024 * Real.exp 4 * ((Nat.log2 (2 * N) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 10) := by
  classical
  let F := SecondRegularCurveComponentGraphs.region P (openRegion E)
  obtain ⟨I, hIS, hdisj, hcover⟩ := FiniteComponentRepresentatives.exists_representatives F S hS
  have hI := SecondRegularComponentFamilyBound.card_bound I P hP E id (fun a ha ↦ hS a (hIS ha))
    ((Fintype.card (TotalDegreeMonomials.Index k) - 1) + 1) havoid
    (fun a ha ↦ hinit a (hIS ha)) hdisj
  let A : ℝ := 2 + 1024 * Real.exp 4 * ((Nat.log2 (2 * N) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 10
  let T := fun a ↦ S.filter (fun z ↦ z ∈ connectedComponentIn F a)
  have hT (a : Fin 2 → ℝ) (ha : a ∈ I) : ((T a).card : ℝ) ≤ A := by
    apply SecondRegularComponentUnitGridCount.point_count P (openRegion E) (openRegion_isOpen E) a
      (hS a (hIS ha)) k hk
      (fun z hz ↦ havoid z (connectedComponentIn_subset F a hz))
      (fun z hz ↦ hWr z (connectedComponentIn_subset F a hz))
      (hinit a (hIS ha)) N hN hlog (T a)
      (fun _ hz ↦ (Finset.mem_filter.mp hz).2)
      (fun z hz i ↦ ((hS z (Finset.mem_filter.mp hz).1).2.1 i).le)
      (fun z hz ↦ hgrid z (Finset.mem_filter.mp hz).1)
  have hc := FiniteCoverCount.cardinal_le S I T A (by
    intro z hz
    obtain ⟨a, ha, hza⟩ := hcover z hz
    exact ⟨a, ha, Finset.mem_filter.mpr ⟨hz, hza⟩⟩) hT
  exact hc.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hI) (by dsimp [A]; positivity))

end PaperP1.RegularComponentPopulationAssembly
