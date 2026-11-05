module

public import PaperP1.Asymptotics.DenseComponentHostCount
public import PaperP1.Asymptotics.UniformGeometricCountsUnderInputs

/-! # Companion T1.7 with no geometric premise for its dense graph clause

General systems and the fixed-number typed component clause still require the
displayed source/ordinary covers and normalized curve count properties.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformGeometricCountsReducedInputs

open PaperP1.UniformGeometricCountStatement

structure Hypotheses (p : Parameters) (K a : ℕ) : Prop where
  systemCover : UniformSourceSurfaceCover.UniformCover p.systemSize K p.systemDegree
  systemCurves : ∀ M, UniformNormalizedCurvePointCount.UniformBound
    ((p.systemDegree + 2).choose 2 + p.systemSize) M
  linearCover : UniformOrdinarySurfaceCover.UniformCover p.linearSize K
  linearCurves : ∀ M, UniformNormalizedCurvePointCount.UniformBound (p.linearSize + 3) M
  typedCover : UniformOrdinarySurfaceCover.UniformCover p.typedSize (a + 1)
  typedCurves : ∀ M, UniformNormalizedCurvePointCount.UniformBound (p.typedSize + 3) M

theorem companion_T1_7 (C A₀ ε η : ℝ) (K Jexp a : ℕ)
    (hA₀ : 0 ≤ A₀) (hε : 0 < ε) (hη : 0 < η) (ha : 0 < a) :
    ∃ p : Parameters, 0 < p.systemDegree ∧ 0 < p.denseDegree ∧ 1 ≤ p.linearSize ∧
      (Hypotheses p K a → Assertions C A₀ ε η K Jexp a p) := by
  obtain ⟨D, kg, kl, hD, hkl, hsystem⟩ :=
    UniformGeometricSystemsUnderInputs.companion_T1_7_systems C A₀ ε K Jexp hA₀ hε
  obtain ⟨kt, htyped⟩ := DegreeOneGraphHostCount.uniform_either_orientation C ε a ha hε
  let p : Parameters := ⟨D, kg, kl, 1, 0, kt⟩
  refine ⟨p, hD, by norm_num [p], hkl, ?_⟩
  intro hgeo
  refine ⟨?_, DenseComponentHostCount.dense_graph_bound C ε η hε hη, ?_,
    FixedPartnerComponentCount.uniform_count C K ε hε,
    UniformGeometricCountsUnderInputs.one_variable K ε hε⟩
  · obtain ⟨A, hA, N₀, h⟩ := hsystem hgeo.systemCover hgeo.systemCurves hgeo.linearCover hgeo.linearCurves
    refine ⟨A, hA, N₀, ?_⟩
    intro N hN L B hband hB hBL n hn s
    exact h N hN L B hband hB hBL n hn s.coefficients s.left s.right s.nonzero
      s.left_disjoint s.right_disjoint s.left_nonempty s.right_nonempty s.degree_cap
      s.left_bound s.right_bound s.coefficient_height s.sourceSet s.targetSet
      s.left_subset s.right_subset s.hosts s.dyadic s.admissible s.roots
  · exact htyped hgeo.typedCover (fun M ↦
      UniformNormalizedCurvePointCount.ordinary_specialization kt M (hgeo.typedCurves M))

end PaperP1.UniformGeometricCountsReducedInputs
