module

public import PaperP1.Arithmetic.OriginalSourceUniformAuxiliary
public import PaperP1.Arithmetic.UniformP3CoverFromAuxiliary

/-! # Uniform actual projected curve and exception covers for original integer sources -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OriginalSourceProjectedCover
open PaperP1 MvPolynomial Finset
open scoped Classical
attribute [local instance] MvPolynomial.gradedAlgebra
local instance indexFinite (k D : ℕ) : Finite (PaperP1.SourceProjectiveEmbedding.GeneratorIndex ℚ (Fin k) D) :=
  PaperP1.SourceProjectiveEmbedding.index_finite ℚ (Fin k) D
local instance indexFintype (k D : ℕ) : Fintype (PaperP1.SourceProjectiveEmbedding.GeneratorIndex ℚ (Fin k) D) := Fintype.ofFinite _

theorem uniform_cover (k powD M : ℕ) (hPowD : 0 < powD) :
    ∀ δ : ℝ, 0 < δ → ∃ (m : ℕ) (A : ℝ), 0 < A ∧
      ∀ s : List (PaperP1.HomogeneousSplitRadicalData.PolynomialRing ℚ), s.length = k →
      ∀ (cZ : Fin s.length → ℤ) (I J : Fin s.length → Finset ℤ),
      (PaperP1.SplitBranchPrimeCertificate.support I J).card ≤ M →
      (Pairwise fun i j ↦ Disjoint (I i) (I j)) →
      (Pairwise fun i j ↦ Disjoint (J i) (J j)) →
      (∀ i, (I i).Nonempty ∨ (J i).Nonempty) →
      ∀ hs : ∀ i, s.get i = PaperP1.HomogeneousSplitRadicalData.radicand (cZ i : ℚ)
        (2*powD-((I i).card+(J i).card)) (I i) (J i),
      ∀ (u : PaperP1.SourceProjectiveEmbedding.GeneratorIndex ℚ (Fin s.length) powD → ℕ)
        (q : MvPolynomial (Fin 4) ℚ),
      PaperP1.LinearHypersurfaceImage.ideal
        (PaperP1.SourceSurfacePowerParameters.parameters s (fun i ↦ (cZ i : ℚ)) powD hPowD I J hs)
        (PaperP1.SourceSurfaceBoundedProjection.primitive (fun i ↦ (cZ i : ℚ)) powD I J u) = Ideal.span {q} →
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) q) →
      q.IsHomogeneous (2 ^ s.length * powD ^ 2) → (finSuccEquiv ℚ 3 q).Monic →
      ∀ (L : Ideal (MvPolynomial (Fin 4) ℚ))
        (hL : L.IsHomogeneous (homogeneousSubmodule (Fin 4) ℚ)),
      letI := HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin 4) ℚ) L hL;
      L = Ideal.span {q} →
      ∀ H : ℕ, 1 ≤ H →
      (∀ b ∈ PaperP1.SplitBranchPrimeCertificate.support I J, |b| ≤ (2 * H ^ 2 : ℕ)) →
      ∀ U : Finset (Fin 4 → ℤ), U ⊆ PaperP1.UniformP3HypersurfaceCover.points q H →
      ∃ (T : Finset (Fin 4 → ℤ))
        (family : Finset (PaperP1.GradedProjectiveCurveData.Curve
          (PaperP1.HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin 4) ℚ) L))),
        T ⊆ U ∧ (∀ Γ ∈ family, Γ.degree ≤ (m : ℚ)) ∧
        (T.card : ℝ) ≤ A * (H : ℝ) ^ (2 / Real.sqrt ((2 ^ k * powD ^ 2 : ℕ) : ℝ) + δ) ∧
        (family.card : ℝ) ≤ A * (H : ℝ) ^ (1 / Real.sqrt ((2 ^ k * powD ^ 2 : ℕ) : ℝ) + δ) ∧
        ∀ v ∈ U, v ∉ T → ∃ Γ ∈ family,
          ∀ P ∈ Γ.ideal.comap (Ideal.Quotient.mk L), eval (fun i ↦ (v i : ℚ)) P = 0 := by
  let d := 2 ^ k * powD ^ 2
  intro δ hδ
  have hδ4 : 0 < δ / 4 := by positivity
  obtain ⟨B, hB, hauxiliary⟩ := OriginalSourceUniformAuxiliary.uniform_auxiliary k powD M hPowD (δ / 4) hδ4
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ4
  obtain ⟨logL, hlogL, hlog⟩ := UniformBinaryLogBudget.absorption 17 (δ / 4) hδ4
  let curveM := m + 1
  let K : ℝ := (d : ℝ) * B
  let C : ℝ := UniformIntegralCurveCount.constant.{0} 4
  let A : ℝ := 1 + K + C * K ^ 2 * logL
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hC : 0 < C := UniformIntegralCurveCount.constant_pos.{0} 4
  have hprod : 0 ≤ C * K ^ 2 * logL := by positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hKA : K ≤ A := by dsimp [A]; linarith only [hprod]
  have hCA : C * K ^ 2 * logL ≤ A := by dsimp [A]; linarith only [hK]
  have hM : 0 < curveM := by dsimp [curveM]; omega
  have hMbudget : 1 / (curveM : ℝ) ≤ δ / 4 := by
    simpa only [curveM, Nat.cast_add, Nat.cast_one] using hm.le
  refine ⟨curveM, A, hA, ?_⟩
  intro s hlen cZ I J hsupport hI hJ hne hs u q hideal hgeom hhom hmonic L hL
  let := HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin 4) ℚ) L hL
  intro hspan H hH hshifts U hU
  obtain ⟨e, G, hG, hnot, he, hzero⟩ := hauxiliary s hlen cZ I J hsupport hI hJ hne hs u q
    hideal hgeom hhom hmonic H hH hshifts
  have hq : q.IsHomogeneous d := by simpa only [d, hlen] using hhom
  have hdegree : q.totalDegree = d := hq.totalDegree (P3HypersurfaceRationalData.irreducible q hgeom).ne_zero
  obtain ⟨T, family, hTU, hdegrees, hcard, hTbound, hcover⟩ := P3SingleAuxiliaryCurveCover.cover_of_equation
    L hL d q hspan hgeom hq hdegree e G hG hnot curveM H hM hH U hU
      (fun v hv ↦ hzero v (hU hv))
  let a : ℝ := 1 / Real.sqrt (d : ℝ)
  have hEd : ((e * d : ℕ) : ℝ) ≤ K * (H : ℝ) ^ (a + δ / 4) := by
    calc
      ((e * d : ℕ) : ℝ) = (d : ℝ) * (e : ℝ) := by push_cast; ring
      _ ≤ (d : ℝ) * (B * (H : ℝ) ^ (a + δ / 4)) :=
        mul_le_mul_of_nonneg_left he (Nat.cast_nonneg d)
      _ = _ := by dsimp [K]; ring
  have hfamily : (family.card : ℝ) ≤ A * (H : ℝ) ^ (a + δ) :=
    (show (family.card : ℝ) ≤ ((e * d : ℕ) : ℝ) by exact_mod_cast hcard).trans
      (P3AuxiliaryCoverExponentBudget.family_bound H hH a δ _ K A hδ.le hK hEd hKA)
  have hT : (T.card : ℝ) ≤ A * (H : ℝ) ^ (2 * a + δ) :=
    hTbound.trans (P3AuxiliaryCoverExponentBudget.exception_bound H hH a δ _ C K logL A
      (Nat.cast_nonneg (e * d)) hC.le hlogL.le hEd (hlog H hH) curveM hMbudget hCA)
  have hexponent : 2 * a + δ = 2 / Real.sqrt (d : ℝ) + δ := by dsimp [a]; ring
  refine ⟨T, family, hTU, hdegrees, ?_, hfamily, hcover⟩
  simpa only [hexponent] using hT

end OriginalSourceProjectedCover
