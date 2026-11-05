module

public import PaperP1.Analysis.RegularComponentPopulationAssembly

/-! # A global quadratic-degree normalized-grid count from actual component geometry -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticNormalizedGridCount

open MvPolynomial Set JointExceptionalComponentGridCount

def componentScale (k N : ℕ) : ℝ :=
  2 + 1024 * Real.exp 4 * ((Nat.log2 (2 * N) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 10

theorem componentScale_nonneg (k N : ℕ) : 0 ≤ componentScale k N := by
  dsimp [componentScale]
  positivity

theorem point_count_with_exceptional_set (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (k : ℕ) (hk : 1 ≤ k) (hkD : k < P.totalDegree) (E : Finset (Fin 2 → ℝ))
    (hE : ∀ z, z ∈ E ↔ z ∈ JointGraphChebyshevExceptions.points P
      (Fintype.card (TotalDegreeMonomials.Index k) - 1) k)
    (N : ℕ) (hN : 0 < N) (hlog : Real.log (N : ℝ) ≤ k)
    (S : Finset (Fin 2 → ℝ)) (hcurve : ∀ z ∈ S, eval z P = 0)
    (hbox : ∀ z ∈ S, z ∈ unitBox)
    (hgrid : ∀ w ∈ S, ∃ z : Fin 2 → ℤ, ∀ i, w i = (z i : ℝ) / N) :
    (S.card : ℝ) ≤ (E.card : ℝ) +
      2 * ((E.card + P.totalDegree * (2 * P.totalDegree + 4) : ℕ) : ℝ) * componentScale k N := by
  classical
  let r := (Fintype.card (TotalDegreeMonomials.Index k) - 1) + 1
  have hboth (z : Fin 2 → ℝ) (hz : z ∉ E) :
      z ∉ GraphControlExceptions.points P r ∧ z ∉ MonomialWronskianExceptions.exceptionalPoints P k :=
    JointGraphChebyshevExceptions.avoids_both P _ k z (fun he ↦ hz ((hE z).mpr he))
  have hgrad (z : Fin 2 → ℝ) (hz : z ∈ S) (hne : z ∉ E) :
      ∃ i, eval z (pderiv i P) ≠ 0 :=
    GraphControlExceptions.gradient_nonzero P (by omega) r z (hcurve z hz) (hboth z hne).1
  let B := S.filter (fun z ↦ z ∈ E)
  let Xs := S.filter (fun z ↦ z ∉ E ∧ |eval z (pderiv 0 P)| ≤ |eval z (pderiv 1 P)|)
  let Ys := S.filter (fun z ↦ z ∉ E ∧ ¬|eval z (pderiv 0 P)| ≤ |eval z (pderiv 1 P)|)
  have hX (z : Fin 2 → ℝ) (hz : z ∈ Xs) :
      z ∈ RegularCurveComponentGraphs.region P (openRegion E) := by
    obtain ⟨hzS, hzE, hcomp⟩ := Finset.mem_filter.mp hz
    refine ⟨⟨hcurve z hzS, ?_⟩, hbox z hzS, hzE⟩
    intro hy
    have hx : eval z (pderiv 0 P) = 0 := abs_eq_zero.mp
      (le_antisymm (by simpa only [hy, abs_zero] using hcomp) (abs_nonneg _))
    obtain ⟨i, hi⟩ := hgrad z hzS hzE
    fin_cases i <;> exact hi (by assumption)
  have hY (z : Fin 2 → ℝ) (hz : z ∈ Ys) :
      z ∈ SecondRegularCurveComponentGraphs.region P (openRegion E) := by
    obtain ⟨hzS, hzE, hcomp⟩ := Finset.mem_filter.mp hz
    refine ⟨⟨hcurve z hzS, ?_⟩, hbox z hzS, hzE⟩
    intro hx
    apply hcomp
    rw [hx, abs_zero]
    exact abs_nonneg _
  have hXcount := RegularComponentPopulationAssembly.first_count P hP E k hk
    (fun z hz ↦ (hboth z hz.2.2).1) (fun z hz ↦ (hboth z hz.2.2).2)
    N hN hlog Xs hX (fun _ hz ↦ (Finset.mem_filter.mp hz).2.2)
    (fun z hz ↦ hgrid z (Finset.mem_filter.mp hz).1)
  have hYcount := RegularComponentPopulationAssembly.second_count P hP E k hk
    (fun z hz ↦ (hboth z hz.2.2).1) (fun z hz ↦ (hboth z hz.2.2).2)
    N hN hlog Ys hY (fun _ hz ↦ (le_of_not_ge (Finset.mem_filter.mp hz).2.2))
    (fun z hz ↦ hgrid z (Finset.mem_filter.mp hz).1)
  have hB : B.card ≤ E.card := Finset.card_le_card (fun _ hz ↦ (Finset.mem_filter.mp hz).2)
  have hcover : S ⊆ (B ∪ Xs) ∪ Ys := by
    intro z hz
    by_cases hzE : z ∈ E
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, hzE⟩))
    · by_cases hcomp : |eval z (pderiv 0 P)| ≤ |eval z (pderiv 1 P)|
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz, hzE, hcomp⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz, hzE, hcomp⟩)
  have hcard : S.card ≤ B.card + Xs.card + Ys.card :=
    (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le B Xs) _))
  have hcardR : (S.card : ℝ) ≤ (B.card : ℝ) + (Xs.card : ℝ) + (Ys.card : ℝ) := by exact_mod_cast hcard
  have hBR : (B.card : ℝ) ≤ (E.card : ℝ) := by exact_mod_cast hB
  change (Xs.card : ℝ) ≤ _ * componentScale k N at hXcount
  change (Ys.card : ℝ) ≤ _ * componentScale k N at hYcount
  linarith only [hcardR, hBR, hXcount, hYcount]

theorem point_count (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (k : ℕ) (hk : 1 ≤ k) (hkD : k < P.totalDegree)
    (N : ℕ) (hN : 0 < N) (hlog : Real.log (N : ℝ) ≤ k)
    (S : Finset (Fin 2 → ℝ)) (hcurve : ∀ z ∈ S, eval z P = 0)
    (hbox : ∀ z ∈ S, z ∈ unitBox)
    (hgrid : ∀ w ∈ S, ∃ z : Fin 2 → ℤ, ∀ i, w i = (z i : ℝ) / N) :
    (S.card : ℝ) ≤ ((P.totalDegree ^ 2 * (123 * (k + 1) ^ 6) : ℕ) : ℝ) +
      2 * (((P.totalDegree ^ 2 * (123 * (k + 1) ^ 6) + P.totalDegree * (2 * P.totalDegree + 4)) : ℕ) : ℝ) *
        componentScale k N := by
  obtain ⟨E, hE, hcard⟩ := JointGraphChebyshevExceptions.exists_finset P hP
    (Fintype.card (TotalDegreeMonomials.Index k) - 1) k hkD
  have hbudget := hcard.trans (Nat.mul_le_mul_left _ (MonomialCountingParameters.exceptional_budget k))
  have hc := point_count_with_exceptional_set P hP k hk hkD E hE N hN hlog S hcurve hbox hgrid
  have hbudgetR : (E.card : ℝ) ≤ ((P.totalDegree ^ 2 * (123 * (k + 1) ^ 6) : ℕ) : ℝ) := by
    exact_mod_cast hbudget
  have hmul := mul_le_mul_of_nonneg_right hbudgetR (componentScale_nonneg k N)
  simp only [Nat.cast_add] at hc ⊢
  nlinarith only [hc, hbudgetR, hmul]

end PaperP1.QuadraticNormalizedGridCount
