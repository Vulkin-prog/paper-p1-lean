module

public import PaperP1.Asymptotics.UniformGeometricCountStatement

/-! # Complete conditional companion T1.7 from the actual systems and actual graph

The one-variable and fixed-partner conclusions are unconditional. Both
two-variable exponents and the first two graph consequences require exactly
the existing ordinary/source covers and normalized curve count.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformGeometricCountsUnderInputs

open PaperP1.UniformGeometricCountStatement

theorem one_variable (K : ℕ) (ε : ℝ) (hε : 0 < ε) : OneVariableBound K ε := by
  obtain ⟨NS, _hNS, hs⟩ := PolynomialSplitKernelCount.single_square_equation 2 K ε hε
  obtain ⟨NT, _hNT, ht⟩ := PolynomialSplitKernelCount.two_square_equations 2 K ε hε
  exact ⟨2 + NS + NT, by omega, fun N hN ↦ ⟨hs N (by omega), ht N (by omega)⟩⟩

theorem companion_T1_7 (C A₀ ε η : ℝ) (K Jexp a : ℕ)
    (hA₀ : 0 ≤ A₀) (hε : 0 < ε) (hη : 0 < η) (ha : 0 < a) :
    ∃ p : Parameters, 0 < p.systemDegree ∧ 0 < p.denseDegree ∧ 1 ≤ p.linearSize ∧
      (Hypotheses p K a η → Assertions C A₀ ε η K Jexp a p) := by
  obtain ⟨D, kg, kl, hD, hkl, hsystem⟩ :=
    UniformGeometricSystemsUnderInputs.companion_T1_7_systems C A₀ ε K Jexp hA₀ hε
  obtain ⟨DG, kd, hDG, hdense⟩ := GeneralGraphHostCount.uniform_dense_hosts C ε η hε hη
  obtain ⟨kt, htyped⟩ := DegreeOneGraphHostCount.uniform_either_orientation C ε a ha hε
  let p : Parameters := ⟨D, kg, kl, DG, kd, kt⟩
  refine ⟨p, hD, hDG, hkl, ?_⟩
  intro hgeo
  refine ⟨?_, hdense hgeo.denseCover hgeo.denseCurves, ?_,
    FixedPartnerComponentCount.uniform_count C K ε hε, one_variable K ε hε⟩
  · obtain ⟨A, hA, N₀, h⟩ := hsystem hgeo.systemCover hgeo.systemCurves hgeo.linearCover hgeo.linearCurves
    refine ⟨A, hA, N₀, ?_⟩
    intro N hN L B hband hB hBL n hn s
    exact h N hN L B hband hB hBL n hn s.coefficients s.left s.right s.nonzero
      s.left_disjoint s.right_disjoint s.left_nonempty s.right_nonempty s.degree_cap
      s.left_bound s.right_bound s.coefficient_height s.sourceSet s.targetSet
      s.left_subset s.right_subset s.hosts s.dyadic s.admissible s.roots
  · exact htyped hgeo.typedCover (fun M ↦
      UniformNormalizedCurvePointCount.ordinary_specialization kt M (hgeo.typedCurves M))

end PaperP1.UniformGeometricCountsUnderInputs
