module

public import PaperP1.Diophantine.UnrestrictedGeometricConicCount
public import PaperP1.Arithmetic.FixedDegreeFieldPlaneCount
public import PaperP1.Asymptotics.BoundedDegreePlaneCounts

/-! # Coefficient- and field-uniform counts for all irreducible plane conics

Neither an embedding into the complex numbers nor absolute irreducibility is
an input. All descent steps use actual finite integer point populations.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FieldConicCount

open Polynomial Finset Filter PolynomialScalarProjection RationalBivariateIrreducibility
open GeometricFactorSwap

theorem rational_geometric_count (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ Q : ℚ[X][X], PlaneCurvePointCount.degree Q = 2 →
      Irreducible Q → Irreducible (extend Q : ℂ[X][X]) →
        ((PlaneCurvePointCount.grid Q N).card : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
  obtain ⟨N₀, hN₀, hcount⟩ := UnrestrictedGeometricConicCount.natural_count ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN Q hdegree hQ hgeo
  obtain ⟨F, n, hn, hF⟩ := IntegralGeometricPlanePointInput.exists_integral_presentation Q
  obtain ⟨hRF, hgeoF, hdeg, hgrid⟩ :=
    IntegralGeometricPlanePointInput.presentation_properties Q hQ hgeo F n hn hF
  have hFne : F ≠ 0 := by
    intro hz
    apply hRF.ne_zero
    simp only [rationalize, hz, Polynomial.map_zero]
  have hFgeo : Geometric F :=
    (HomogenizationIrreducibilityReflection.geometric_iff_affine F hFne).mpr (by
      rw [← ComplexProjectiveIrreducibility.rational_extension]
      exact hgeoF)
  have hb := hcount N hN F (hdeg.trans hdegree) hFgeo
  simpa only [hgrid] using hb

theorem rational_count (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ Q : ℚ[X][X], PlaneCurvePointCount.degree Q = 2 →
      Irreducible Q → ((PlaneCurvePointCount.grid Q N).card : ℝ) ≤
        (N : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
  obtain ⟨Ng, _hNg, hcount⟩ := rational_geometric_count ε hε
  have ht := ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < (1 : ℝ) / 2 + ε)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop (4 : ℝ))
  obtain ⟨Nc, hc⟩ := eventually_atTop.mp ht
  refine ⟨max 3 (max Ng Nc), by omega, ?_⟩
  intro N hN Q hdegree hQ
  by_cases hgeo : Irreducible (extend Q : ℂ[X][X])
  · exact hcount N (by omega) Q hdegree hQ hgeo
  · have hb := NonGeometricPlanePointBound.grid_card Q hQ hgeo N
    rw [hdegree] at hb
    have hsmall : ((PlaneCurvePointCount.grid Q N).card : ℝ) ≤ 4 := by
      norm_num at hb
      exact_mod_cast (hb.trans (by decide : 2 ≤ 4))
    exact hsmall.trans (hc N (by omega))

theorem field_count (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ (F : Type*) [Field F] [CharZero F], ∀ P : F[X][X],
      PlaneCurvePointCount.degree P = 2 → Irreducible P →
        ((PlaneCurvePointCount.grid P N).card : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
  classical
  obtain ⟨Nq, _hNq, hcount⟩ := rational_count ε hε
  have ht := ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < (1 : ℝ) / 2 + ε)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop (4 : ℝ))
  obtain ⟨Nc, hc⟩ := eventually_atTop.mp ht
  refine ⟨max 3 (max Nq Nc), by omega, ?_⟩
  intro N hN F _hF _hchar P hdegree hP
  let S := PlaneCurvePointCount.grid P N
  by_cases hsmall : S.card ≤ 4
  · have hs : (S.card : ℝ) ≤ 4 := by exact_mod_cast hsmall
    exact hs.trans (hc N (by omega))
  let f : ℤ × ℤ → ℚ × ℚ := fun z ↦ ((z.1 : ℚ), (z.2 : ℚ))
  have hi : Function.Injective f := by
    intro z w he
    exact Prod.ext (Int.cast_injective (congrArg Prod.fst he))
      (Int.cast_injective (congrArg Prod.snd he))
  have hpoints : ∀ z ∈ S.image f, P.evalEval (algebraMap ℚ F z.1) (algebraMap ℚ F z.2) = 0 := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    have hh := ((PlaneCurvePointCount.mem_grid P N w).mp hw).2.2
    simpa only [f, map_intCast] using hh
  obtain ⟨Q, hQ, _hassoc, hdeg, hzero⟩ :=
    ManyPointsScalarDescent.many_points_descent P hP (S.image f) hpoints
      (by rw [card_image_of_injective _ hi, hdegree]; omega)
  have hsub : S ⊆ PlaneCurvePointCount.grid Q N := by
    intro z hz
    have hb := (PlaneCurvePointCount.mem_grid P N z).mp hz
    exact (PlaneCurvePointCount.mem_grid Q N z).mpr
      ⟨hb.1, hb.2.1, hzero (f z) (mem_image.mpr ⟨z, hz, rfl⟩)⟩
  have hs : (S.card : ℝ) ≤ ((PlaneCurvePointCount.grid Q N).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  exact hs.trans (hcount N (by omega) Q (hdeg.trans hdegree) hQ)

theorem finite_population_count (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ (F : Type*) [Field F] [CharZero F], ∀ P : F[X][X],
      PlaneCurvePointCount.degree P = 2 → Irreducible P → ∀ S : Finset (ℤ × ℤ),
      (∀ z ∈ S, P.evalEval (z.1 : F) (z.2 : F) = 0 ∧ z.1.natAbs ≤ N ∧ z.2.natAbs ≤ N) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
  obtain ⟨N₀, hN₀, hcount⟩ := field_count ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN F _hF _hchar P hD hP S hS
  have hsub : S ⊆ PlaneCurvePointCount.grid P N := by
    intro z hz
    have hh := hS z hz
    apply (PlaneCurvePointCount.mem_grid P N z).mpr
    refine ⟨?_, ?_, hh.1⟩
    · rw [Int.abs_eq_natAbs]
      exact_mod_cast hh.2.1
    · rw [Int.abs_eq_natAbs]
      exact_mod_cast hh.2.2
  have hc : (S.card : ℝ) ≤ ((PlaneCurvePointCount.grid P N).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  exact hc.trans (hcount N hN F P hD hP)

theorem real_height_count (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (F : Type*) [Field F] [CharZero F], ∀ P : F[X][X],
      PlaneCurvePointCount.degree P = 2 → Irreducible P → ∀ H : ℝ, 2 < H →
        ((PlaneCurvePointCount.grid P ⌊H⌋₊).card : ℝ) ≤ A * H ^ ((1 : ℝ) / 2 + ε) := by
  obtain ⟨N₀, hN₀, hcount⟩ := field_count ε hε
  let A : ℝ := ((2 * N₀ + 1 : ℕ) : ℝ) ^ 2
  have hA : 1 ≤ A := by
    dsimp only [A]
    exact_mod_cast Nat.one_le_pow 2 (2 * N₀ + 1) (by omega)
  refine ⟨A, hA, ?_⟩
  intro F _hF _hchar P hD hP H hH
  have hpow : (1 : ℝ) ≤ H ^ ((1 : ℝ) / 2 + ε) := Real.one_le_rpow (by linarith) (by positivity)
  by_cases hlarge : N₀ ≤ ⌊H⌋₊
  · have hb := hcount ⌊H⌋₊ hlarge F P hD hP
    have hp : (⌊H⌋₊ : ℝ) ^ ((1 : ℝ) / 2 + ε) ≤ H ^ ((1 : ℝ) / 2 + ε) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) (by positivity)
    exact (hb.trans hp).trans (le_mul_of_one_le_left (by positivity) hA)
  · have hsub : PlaneCurvePointCount.grid P ⌊H⌋₊ ⊆
        (CurveIntegerFibres.offsetBox N₀) ×ˢ (CurveIntegerFibres.offsetBox N₀) := by
      intro z hz
      have hb := (PlaneCurvePointCount.mem_grid P ⌊H⌋₊ z).mp hz
      have hceil : (⌊H⌋₊ : ℤ) ≤ (N₀ : ℤ) := by exact_mod_cast (show ⌊H⌋₊ ≤ N₀ by omega)
      exact mem_product.mpr ⟨(CurveIntegerFibres.mem_offsetBox N₀ z.1).mpr (hb.1.trans hceil),
        (CurveIntegerFibres.mem_offsetBox N₀ z.2).mpr (hb.2.1.trans hceil)⟩
    have hb : ((PlaneCurvePointCount.grid P ⌊H⌋₊).card : ℝ) ≤ A := by
      have hc := card_le_card hsub
      rw [card_product, LinearPlaneGridBound.offsetBox_card] at hc
      dsimp only [A]
      rw [pow_two]
      exact_mod_cast hc
    exact hb.trans (le_mul_of_one_le_right (by positivity) hpow)

theorem uniform_sublinear (η : ℝ) (hη : 0 < η) :
    ∃ H₀ : ℝ, 2 < H₀ ∧ ∀ H ≥ H₀, ∀ (F : Type*) [Field F] [CharZero F], ∀ P : F[X][X],
      PlaneCurvePointCount.degree P = 2 → Irreducible P →
        ((PlaneCurvePointCount.grid P ⌊H⌋₊).card : ℝ) ≤ η * H := by
  obtain ⟨A, _hA, hcount⟩ := real_height_count (1 / 4) (by norm_num)
  obtain ⟨H₀, hH₀, hsmall⟩ := BoundedDegreePlaneCounts.eventual_power_absorption
    (A / η) (3 / 4) 1 (by norm_num)
  refine ⟨H₀, hH₀, ?_⟩
  intro H hH F _hF _hchar P hD hP
  have hb := hcount F P hD hP H (hH₀.trans_le hH)
  norm_num only [show (1 : ℝ) / 2 + 1 / 4 = 3 / 4 by norm_num] at hb
  have hs := mul_le_mul_of_nonneg_left (hsmall H hH) hη.le
  have hcancel : η * (A / η) = A := by field_simp
  rw [← mul_assoc, hcancel, Real.rpow_one] at hs
  exact hb.trans hs

end PaperP1.FieldConicCount
