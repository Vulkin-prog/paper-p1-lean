module

public import PaperP1.Arithmetic.UniformP3FiniteFieldCertificate
public import PaperP1.Algebra.P3UniformIntegerAuxiliary
public import PaperP1.Algebra.P3ModelCoefficientGrowth
public import PaperP1.Algebra.NonzeroScalarPolynomial
public import PaperP1.Geometry.P3HypersurfaceRationalData

/-! # The complete global auxiliary hypersurface theorem reduces to an independent finite-field certificate budget -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformP3AuxiliaryFromFiniteFieldCertificate

open MvPolynomial Finset
open scoped Classical

theorem positive_degree (d : ℕ) (hd : 0 < d)
    (hbudget : UniformP3FiniteFieldCertificate.UniformBudget d) :
    UniformP3AuxiliaryHypersurface.UniformAuxiliary d := by
  intro ε hε
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let t := Real.sqrt (d : ℝ)
  have ht : 0 < t := Real.sqrt_pos.mpr hdR
  have htsq : t ^ 2 = (d : ℝ) := Real.sq_sqrt hdR.le
  let β : ℝ := 1 / t + ε
  have hβ : 0 < β := by dsimp only [β]; positivity
  have hβt : 1 < β * t := by
    calc
      1 < 1 + ε * t := lt_add_of_pos_right 1 (mul_pos hε ht)
      _ = β * t := by dsimp only [β]; rw [add_mul, div_mul_cancel₀ 1 ht.ne']
  have hgap : 1 < (d : ℝ) * β ^ 2 := by
    have hh : 1 < (β * t) ^ 2 := by nlinarith
    have he : (β * t) ^ 2 = (d : ℝ) * β ^ 2 := by rw [mul_pow, htsq]; ring
    rwa [he] at hh
  let η : ℝ := ((d : ℝ) * β ^ 2 - 1) / 2
  have hη : 0 < η := by dsimp only [η]; linarith
  let D : ℝ := 1 + η
  have hD : 0 < D := by dsimp only [D]; positivity
  have hmargin : Real.sqrt (D / (d : ℝ)) < β := by
    apply (Real.sqrt_lt' hβ).mpr
    apply (div_lt_iff₀ hdR).mpr
    dsimp only [D, η]
    nlinarith only [hgap]
  obtain ⟨T, N, K₀, hT, hcertificate⟩ := hbudget η hη
  let T₁ := P3ModelCoefficientGrowth.constant d
  let c₁ := P3ModelCoefficientGrowth.exponent d
  let T₀ := T * T₁ ^ N
  let c₀ := c₁ * N
  have hT₁ : 0 < T₁ := P3ModelCoefficientGrowth.constant_pos d
  have hT₀ : 0 < T₀ := Nat.mul_pos hT (pow_pos hT₁ N)
  obtain ⟨C₀, hC₀, haux⟩ := P3UniformIntegerAuxiliary.uniform_degree d hd D β hD hβ hmargin
    T₀ c₀ T₁ c₁ K₀ hT₀ hT₁
  refine ⟨C₀ + (d : ℝ), by positivity, ?_⟩
  intro q hgeom hhom _hdegree H hH
  have hirr := P3HypersurfaceRationalData.irreducible q hgeom
  have hq0 : q ≠ 0 := hirr.ne_zero
  by_cases hx : X (3 : Fin 4) ∣ q
  · have hX : Irreducible (X (3 : Fin 4) : MvPolynomial (Fin 4) ℚ) :=
      (prime_X (i := (3 : Fin 4))).irreducible
    have hqX : q ∣ X (3 : Fin 4) := (hX.associated_of_dvd hirr hx).symm.dvd
    have hempty := P3HeightLeadingMonomial.points_empty_of_dvd_coordinate q hqX H
    refine ⟨0, 1, isHomogeneous_one _ _, ?_, ?_, ?_⟩
    · exact fun hh ↦ hirr.not_isUnit (isUnit_of_dvd_one hh)
    · simp only [Nat.cast_zero]
      change (0 : ℝ) ≤ (C₀ + (d : ℝ)) * (H : ℝ) ^ β
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg H) β)
    · intro v hv
      rw [hempty] at hv
      simp at hv
  let U := UniformP3HypersurfaceCover.points q H
  have hheight (v : Fin 4 → ℤ) (hv : v ∈ U) : ∀ k, |v k| ≤ (H : ℤ) :=
    ((UniformP3HypersurfaceCover.mem_points q H v).mp hv).1
  have hnormal (v : Fin 4 → ℤ) (hv : v ∈ U) : v 3 = 1 :=
    ((UniformP3HypersurfaceCover.mem_points q H v).mp hv).2.1
  have hroots (v : Fin 4 → ℤ) (hv : v ∈ U) : eval (fun k ↦ (v k : ℚ)) q = 0 :=
    ((UniformP3HypersurfaceCover.mem_points q H v).mp hv).2.2
  obtain ⟨P, hP, hP0, hcoef, hzero, hor⟩ := P3HeightControlledEquation.exists_model_or_auxiliary
    d H hH U hheight q hhom hq0 hroots
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hpow : 1 ≤ (H : ℝ) ^ β := Real.one_le_rpow hHR hβ.le
  rcases hor with hnot | ⟨c, hc, hmodel⟩
  · refine ⟨d, map (Int.castRingHom ℚ) P, hP.map _, hnot, ?_, ?_⟩
    · change (d : ℝ) ≤ (C₀ + (d : ℝ)) * (H : ℝ) ^ β
      calc
        (d : ℝ) ≤ (d : ℝ) * (H : ℝ) ^ β := by nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg H) β)
    · intro v hv
      rw [P3HeightControlledEquation.integer_evaluation, hzero v hv, Int.cast_zero]
  let A := T₁ * H ^ c₁
  have hA : 0 < A := Nat.mul_pos hT₁ (pow_pos (by omega : 0 < H) c₁)
  have hcoeffA : ∀ m, |P.coeff m| ≤ (A : ℤ) := by
    intro m
    simpa only [P3ModelCoefficientGrowth.bound_eq, A, T₁, c₁] using hcoef m
  have hirrP : Irreducible (map (Int.castRingHom ℚ) P) := by
    rw [hmodel]
    exact (NonzeroScalarPolynomial.irreducible_scalar c hc q).mpr hirr
  have hcmap : algebraMap ℚ (AlgebraicClosure ℚ) c ≠ 0 := by
    intro hz
    apply hc
    apply (algebraMap ℚ (AlgebraicClosure ℚ)).injective
    simpa only [map_zero] using hz
  have hgeomP : Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) (map (Int.castRingHom ℚ) P)) := by
    rw [hmodel, map_mul, map_C]
    exact (NonzeroScalarPolynomial.irreducible_scalar _ hcmap _).mpr hgeom
  obtain ⟨z, hz, hzbound, hclasses⟩ := hcertificate A hA P hgeomP hP hcoeffA
  have hzheight : z.natAbs ≤ T₀ * H ^ c₀ := by
    calc
      _ ≤ T * A ^ N := hzbound
      _ = _ := by simpa only [A, T₁, c₁, T₀, c₀] using P3ModelCoefficientGrowth.certificate_growth d T N H
  have hnotP : ¬X (3 : Fin 4) ∣ map (Int.castRingHom ℚ) P := by
    rw [hmodel]
    exact fun hh ↦ hx ((NonzeroScalarPolynomial.dvd_scalar_right c hc _ q).mp hh)
  obtain ⟨e, G, _hed, hGe, hGnot, hGzero, heC⟩ := haux H hH A hA le_rfl P hP0 hP hnotP hirrP hcoeffA
    z hz hzheight hclasses U hnormal hheight hzero
  refine ⟨e, map (Int.castRingHom ℚ) G, hGe.map _, ?_, ?_, ?_⟩
  · intro hh
    apply hGnot
    rw [hmodel]
    exact (NonzeroScalarPolynomial.scalar_dvd c hc q _).mpr hh
  · change (e : ℝ) ≤ (C₀ + (d : ℝ)) * (H : ℝ) ^ β
    exact heC.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Nat.cast_nonneg d))
      (Real.rpow_nonneg (Nat.cast_nonneg H) β))
  · intro v hv
    rw [P3HeightControlledEquation.integer_evaluation, hGzero v hv, Int.cast_zero]

theorem uniform_auxiliary (d : ℕ) (hbudget : UniformP3FiniteFieldCertificate.UniformBudget d) :
    UniformP3AuxiliaryHypersurface.UniformAuxiliary d := by
  by_cases hd : 0 < d
  · exact positive_degree d hd hbudget
  · intro ε _hε
    refine ⟨1, by norm_num, ?_⟩
    intro q hgeom _hhom hdegree _H _hH
    have hh := P3HypersurfaceRationalData.degree_pos q hgeom d hdegree
    omega

end PaperP1.UniformP3AuxiliaryFromFiniteFieldCertificate
