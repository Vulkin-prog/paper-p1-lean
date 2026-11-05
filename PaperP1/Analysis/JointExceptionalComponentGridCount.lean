module

public import PaperP1.Analysis.RegularComponentUnitGridCount
public import PaperP1.Analysis.SecondRegularComponentUnitGridCount
public import PaperP1.Analysis.MonomialCountingParameters

/-! # Internally controlled actual regular components outside a genuine finite exceptional set -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.JointExceptionalComponentGridCount

open MvPolynomial Set RegularCurveComponentGraphs


def unitBox : Set (Fin 2 → ℝ) := {z | ∀ i, |z i| < 1}

def openRegion (E : Finset (Fin 2 → ℝ)) : Set (Fin 2 → ℝ) := unitBox ∩ (E : Set (Fin 2 → ℝ))ᶜ

theorem unitBox_isOpen : IsOpen unitBox := by
  have he : unitBox = ⋂ i : Fin 2, {z : Fin 2 → ℝ | |z i| < 1} := by
    ext z
    simp [unitBox]
  rw [he]
  exact isOpen_iInter_of_finite (fun i ↦ isOpen_lt (continuous_apply i).abs continuous_const)

theorem openRegion_isOpen (E : Finset (Fin 2 → ℝ)) : IsOpen (openRegion E) :=
  unitBox_isOpen.inter E.finite_toSet.isClosed.isOpen_compl

theorem exists_first_component_count (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (k : ℕ) (hk : 1 ≤ k) (hkD : k < P.totalDegree) :
    ∃ E : Finset (Fin 2 → ℝ),
      (∀ z, z ∈ E ↔ z ∈ JointGraphChebyshevExceptions.points P (Fintype.card (TotalDegreeMonomials.Index k) - 1) k) ∧
      E.card ≤ P.totalDegree ^ 2 * (123 * (k + 1) ^ 6) ∧
      ∀ anchor : Fin 2 → ℝ, eval anchor P = 0 → anchor ∈ unitBox → anchor ∉ E →
        |eval anchor (pderiv 0 P)| ≤ |eval anchor (pderiv 1 P)| →
        ∀ N : ℕ, 0 < N → Real.log (N : ℝ) ≤ k → ∀ S : Finset (Fin 2 → ℝ),
          (∀ w ∈ S, w ∈ connectedComponentIn (region P (openRegion E)) anchor) →
          (∀ w ∈ S, ∃ z : Fin 2 → ℤ, ∀ i, w i = (z i : ℝ) / N) →
          (S.card : ℝ) ≤ 2 + 1024 * Real.exp 4 * ((Nat.log2 (2 * N) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 10 := by
  classical
  obtain ⟨E, hE, hcard⟩ := JointGraphChebyshevExceptions.exists_finset P hP
    (Fintype.card (TotalDegreeMonomials.Index k) - 1) k hkD
  refine ⟨E, hE, hcard.trans (Nat.mul_le_mul_left _ (MonomialCountingParameters.exceptional_budget k)), ?_⟩
  intro anchor hzero hboxa hnot hinit N hN hlog S hS hgrid
  have hD : 0 < P.totalDegree := by omega
  have hnotJoint : anchor ∉ JointGraphChebyshevExceptions.points P (Fintype.card (TotalDegreeMonomials.Index k) - 1) k :=
    fun hz ↦ hnot ((hE anchor).mpr hz)
  have hcontrol := (JointGraphChebyshevExceptions.avoids_both P
    (Fintype.card (TotalDegreeMonomials.Index k) - 1) k anchor hnotJoint).1
  have hgradient := GraphControlExceptions.gradient_nonzero P hD
    ((Fintype.card (TotalDegreeMonomials.Index k) - 1) + 1) anchor hzero hcontrol
  have hPy : eval anchor (pderiv 1 P) ≠ 0 := by
    intro hz
    have hPx : eval anchor (pderiv 0 P) = 0 := abs_eq_zero.mp
      (le_antisymm (by simpa only [hz, abs_zero] using hinit) (abs_nonneg _))
    obtain ⟨i, hi⟩ := hgradient
    fin_cases i
    · exact hi hPx
    · exact hi hz
  have ha : anchor ∈ region P (openRegion E) := ⟨⟨hzero, hPy⟩, hboxa, hnot⟩
  have hboth (w : Fin 2 → ℝ) (hw : w ∈ connectedComponentIn (region P (openRegion E)) anchor) :
      w ∉ GraphControlExceptions.points P ((Fintype.card (TotalDegreeMonomials.Index k) - 1) + 1) ∧
        w ∉ MonomialWronskianExceptions.exceptionalPoints P k := by
    have hregion := connectedComponentIn_subset (region P (openRegion E)) anchor hw
    have hnotE : w ∉ E := hregion.2.2
    exact JointGraphChebyshevExceptions.avoids_both P (Fintype.card (TotalDegreeMonomials.Index k) - 1) k w
      (fun hz ↦ hnotE ((hE w).mpr hz))
  have hboxS : ∀ w ∈ S, ∀ i, |w i| ≤ 1 := by
    intro w hw i
    have hregion := connectedComponentIn_subset (region P (openRegion E)) anchor (hS w hw)
    exact (hregion.2.1 i).le
  exact RegularComponentUnitGridCount.point_count P (openRegion E) (openRegion_isOpen E) anchor ha k hk
    (fun w hw ↦ (hboth w hw).1) (fun w hw ↦ (hboth w hw).2) hinit N hN hlog S hS hboxS hgrid

theorem exists_second_component_count (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (k : ℕ) (hk : 1 ≤ k) (hkD : k < P.totalDegree) :
    ∃ E : Finset (Fin 2 → ℝ),
      (∀ z, z ∈ E ↔ z ∈ JointGraphChebyshevExceptions.points P (Fintype.card (TotalDegreeMonomials.Index k) - 1) k) ∧
      E.card ≤ P.totalDegree ^ 2 * (123 * (k + 1) ^ 6) ∧
      ∀ anchor : Fin 2 → ℝ, eval anchor P = 0 → anchor ∈ unitBox → anchor ∉ E →
        |eval anchor (pderiv 1 P)| ≤ |eval anchor (pderiv 0 P)| →
        ∀ N : ℕ, 0 < N → Real.log (N : ℝ) ≤ k → ∀ S : Finset (Fin 2 → ℝ),
          (∀ w ∈ S, w ∈ connectedComponentIn (SecondRegularCurveComponentGraphs.region P (openRegion E)) anchor) →
          (∀ w ∈ S, ∃ z : Fin 2 → ℤ, ∀ i, w i = (z i : ℝ) / N) →
          (S.card : ℝ) ≤ 2 + 1024 * Real.exp 4 * ((Nat.log2 (2 * N) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 10 := by
  classical
  obtain ⟨E, hE, hcard⟩ := JointGraphChebyshevExceptions.exists_finset P hP
    (Fintype.card (TotalDegreeMonomials.Index k) - 1) k hkD
  refine ⟨E, hE, hcard.trans (Nat.mul_le_mul_left _ (MonomialCountingParameters.exceptional_budget k)), ?_⟩
  intro anchor hzero hboxa hnot hinit N hN hlog S hS hgrid
  have hD : 0 < P.totalDegree := by omega
  have hnotJoint : anchor ∉ JointGraphChebyshevExceptions.points P (Fintype.card (TotalDegreeMonomials.Index k) - 1) k :=
    fun hz ↦ hnot ((hE anchor).mpr hz)
  have hcontrol := (JointGraphChebyshevExceptions.avoids_both P
    (Fintype.card (TotalDegreeMonomials.Index k) - 1) k anchor hnotJoint).1
  have hgradient := GraphControlExceptions.gradient_nonzero P hD
    ((Fintype.card (TotalDegreeMonomials.Index k) - 1) + 1) anchor hzero hcontrol
  have hPx : eval anchor (pderiv 0 P) ≠ 0 := by
    intro hz
    have hPy : eval anchor (pderiv 1 P) = 0 := abs_eq_zero.mp
      (le_antisymm (by simpa only [hz, abs_zero] using hinit) (abs_nonneg _))
    obtain ⟨i, hi⟩ := hgradient
    fin_cases i
    · exact hi hz
    · exact hi hPy
  have ha : anchor ∈ SecondRegularCurveComponentGraphs.region P (openRegion E) := ⟨⟨hzero, hPx⟩, hboxa, hnot⟩
  have hboth (w : Fin 2 → ℝ) (hw : w ∈ connectedComponentIn (SecondRegularCurveComponentGraphs.region P (openRegion E)) anchor) :
      w ∉ GraphControlExceptions.points P ((Fintype.card (TotalDegreeMonomials.Index k) - 1) + 1) ∧
        w ∉ MonomialWronskianExceptions.exceptionalPoints P k := by
    have hregion := connectedComponentIn_subset (SecondRegularCurveComponentGraphs.region P (openRegion E)) anchor hw
    have hnotE : w ∉ E := hregion.2.2
    exact JointGraphChebyshevExceptions.avoids_both P (Fintype.card (TotalDegreeMonomials.Index k) - 1) k w
      (fun hz ↦ hnotE ((hE w).mpr hz))
  have hboxS : ∀ w ∈ S, ∀ i, |w i| ≤ 1 := by
    intro w hw i
    have hregion := connectedComponentIn_subset (SecondRegularCurveComponentGraphs.region P (openRegion E)) anchor (hS w hw)
    exact (hregion.2.1 i).le
  exact SecondRegularComponentUnitGridCount.point_count P (openRegion E) (openRegion_isOpen E) anchor ha k hk
    (fun w hw ↦ (hboth w hw).1) (fun w hw ↦ (hboth w hw).2) hinit N hN hlog S hS hboxS hgrid



theorem exists_common_component_counts (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (k : ℕ) (hk : 1 ≤ k) (hkD : k < P.totalDegree) :
    ∃ E : Finset (Fin 2 → ℝ),
      (∀ z, z ∈ E ↔ z ∈ JointGraphChebyshevExceptions.points P (Fintype.card (TotalDegreeMonomials.Index k) - 1) k) ∧
      E.card ≤ P.totalDegree ^ 2 * (123 * (k + 1) ^ 6) ∧
      (∀ anchor : Fin 2 → ℝ, eval anchor P = 0 → anchor ∈ unitBox → anchor ∉ E →
        |eval anchor (pderiv 0 P)| ≤ |eval anchor (pderiv 1 P)| →
        ∀ N : ℕ, 0 < N → Real.log (N : ℝ) ≤ k → ∀ S : Finset (Fin 2 → ℝ),
          (∀ w ∈ S, w ∈ connectedComponentIn (region P (openRegion E)) anchor) →
          (∀ w ∈ S, ∃ z : Fin 2 → ℤ, ∀ i, w i = (z i : ℝ) / N) →
          (S.card : ℝ) ≤ 2 + 1024 * Real.exp 4 * ((Nat.log2 (2 * N) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 10) ∧
      (∀ anchor : Fin 2 → ℝ, eval anchor P = 0 → anchor ∈ unitBox → anchor ∉ E →
        |eval anchor (pderiv 1 P)| ≤ |eval anchor (pderiv 0 P)| →
        ∀ N : ℕ, 0 < N → Real.log (N : ℝ) ≤ k → ∀ S : Finset (Fin 2 → ℝ),
          (∀ w ∈ S, w ∈ connectedComponentIn (SecondRegularCurveComponentGraphs.region P (openRegion E)) anchor) →
          (∀ w ∈ S, ∃ z : Fin 2 → ℤ, ∀ i, w i = (z i : ℝ) / N) →
          (S.card : ℝ) ≤ 2 + 1024 * Real.exp 4 * ((Nat.log2 (2 * N) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 10) := by
  classical
  obtain ⟨E, hE, hcard, hfirst⟩ := exists_first_component_count P hP k hk hkD
  obtain ⟨F, hF, _hFcard, hsecond⟩ := exists_second_component_count P hP k hk hkD
  have hFE : F = E := by
    ext z
    rw [hF z, hE z]
  subst F
  exact ⟨E, hE, hcard, hfirst, hsecond⟩

end PaperP1.JointExceptionalComponentGridCount
