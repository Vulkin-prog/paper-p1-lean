module

public import PaperP1.Arithmetic.UniformSourceCurvePointCount
public import PaperP1.Geometry.SourceIntegerCurvePoint
public import PaperP1.Combinatorics.FiniteCoverCount

/-! # Counting literal source lifts on an actual finite curve cover using the proved 2D degree gap

The generic uniform curve property is an explicit unproved argument. An actual
finite covering collection is data here; no surface-cover theorem is asserted.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceCurvePointCover

open Finset PaperP1.HomogeneousSplitRadicalData PaperP1.SourceProjectiveCurveData
  PaperP1.SplitRadicalPointHeight PaperP1.SelectedProportionalPairs

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance

def Admissible (S T : Finset ℤ) (p : ℤ × ℤ) : Prop :=
  (∀ z ∈ S, 0 < p.1 + z) ∧ (∀ z ∈ T, 0 < p.2 + z) ∧
    EvenIndependentValues.Independent (values p.1 S) ∧ EvenIndependentValues.Independent (values p.2 T) ∧
    Disjoint (FiniteEvenSquareClasses.space (values p.1 S)) (FiniteEvenSquareClasses.space (values p.2 T))

theorem finite_cover_bound (kmax D M : ℕ) (hD : 0 < D) (δ : ℝ) (hδ : 0 < δ)
    (hPila : UniformNormalizedCurvePointCount.UniformBound ((D + 2).choose 2 + kmax) M) :
    ∃ A : ℝ, 0 < A ∧ ∀ s : List (PolynomialRing ℚ), s.length ≤ kmax → 2 ≤ s.length →
      ∀ (d : Fin s.length → ℤ) (I J : Fin s.length → Finset ℤ),
      ∀ (hs : ∀ i, s.get i = radicand (d i : ℚ) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
        (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D),
      (∀ i, d i ≠ 0) → (Pairwise fun i j ↦ Disjoint (I i) (I j)) →
      (Pairwise fun i j ↦ Disjoint (J i) (J j)) → (∀ i, (I i).Nonempty) → (∀ i, (J i).Nonempty) →
      ∀ S T : Finset ℤ, (∀ i, I i ⊆ S) → (∀ i, J i ⊆ T) →
      ∀ (F : Finset (ℤ × ℤ)) (w : ℤ × ℤ → Fin s.length → ℤ), (∀ p ∈ F, Admissible S T p) →
      (∀ p ∈ F, ∀ i, w p i ^ 2 = d i * integerProduct (I i) p.1 * integerProduct (J i) p.2) →
      ∀ (V : Finset (SourceProjectiveEmbedding.GeneratorIndex ℚ (Fin s.length) D → ℤ))
        (curves : Finset (Curve s (fun i ↦ (d i : ℚ)) D I J hdeg hD)) (H : ℕ), 1 ≤ H →
      (∀ Γ ∈ curves, degree s (fun i ↦ (d i : ℚ)) D I J hs hdeg hD Γ ≤ (M : ℚ)) →
      (∀ p ∈ F, SourceIntegerLift.point D p.1 p.2 (w p) ∉ V → ∃ Γ ∈ curves,
        SourceIntegerLift.point D p.1 p.2 (w p) ∈ SourceIntegerPoints.curvePoints D
          (ideal s (fun i ↦ (d i : ℚ)) D I J hdeg hD Γ) H) →
      (F.card : ℝ) ≤ (V.card : ℝ) + (curves.card : ℝ) * A * (H : ℝ) ^ (1 / (2 * (D : ℝ)) + δ) := by
  obtain ⟨A, hA, hpoint⟩ := UniformSourceCurvePointCount.uniform_bound kmax D M hPila δ hδ
  refine ⟨A, hA, ?_⟩
  intro s hlength hcard d I J hs hdeg hd hI hJ hneI hneJ S T hiS hjT F w hadmiss hroot V curves H hH hM hcover
  classical
  let U := F.image fun p ↦ SourceIntegerLift.point D p.1 p.2 (w p)
  let large := curves.filter fun Γ ↦ 2 * (D : ℚ) ≤ degree s (fun i ↦ (d i : ℚ)) D I J hs hdeg hD Γ
  have hlarge_cover : ∀ v ∈ U \ V, ∃ Γ ∈ large, v ∈ SourceIntegerPoints.curvePoints D
      (ideal s (fun i ↦ (d i : ℚ)) D I J hdeg hD Γ) H := by
    intro v hv
    obtain ⟨hvU, hvV⟩ := mem_sdiff.mp hv
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hvU
    obtain ⟨Γ, hΓ, hvΓ⟩ := hcover p hp hvV
    have hker := (SourceIntegerPoints.mem_curvePoints D _ H _).mp hvΓ |>.2
    obtain ⟨hposS, hposT, hindS, hindT, hdirect⟩ := hadmiss p hp
    have hdegree := SourceIntegerCurvePoint.embedded_degree_lower s d D I J hs hdeg hD
      p.1 p.2 (w p) (hroot p hp) Γ.point Γ.height hker hcard S T hiS hjT hI hJ hneI hneJ
      hposS hposT hindS hindT hdirect hd
    exact ⟨Γ, mem_filter.mpr ⟨hΓ, hdegree⟩, hvΓ⟩
  have hbound : ∀ Γ ∈ large,
      ((SourceIntegerPoints.curvePoints D (ideal s (fun i ↦ (d i : ℚ)) D I J hdeg hD Γ) H).card : ℝ) ≤
        A * (H : ℝ) ^ (1 / (2 * (D : ℝ)) + δ) := by
    intro Γ hΓ
    obtain ⟨hΓmem, hdegree⟩ := mem_filter.mp hΓ
    have hdegreeR : 2 * (D : ℝ) ≤ (degree s (fun i ↦ (d i : ℚ)) D I J hs hdeg hD Γ : ℝ) := by
      exact_mod_cast hdegree
    have hHreal : (1 : ℝ) ≤ H := by exact_mod_cast hH
    exact (hpoint s hlength (fun i ↦ (d i : ℚ)) I J hs hdeg hD Γ (hM Γ hΓmem) H hH).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hHreal
        (add_le_add (one_div_le_one_div_of_le (by positivity) hdegreeR) (le_refl δ))) hA.le)
  have hcount := FiniteCoverCount.cardinal_le (U \ V) large
    (fun Γ ↦ SourceIntegerPoints.curvePoints D (ideal s (fun i ↦ (d i : ℚ)) D I J hdeg hD Γ) H)
    (A * (H : ℝ) ^ (1 / (2 * (D : ℝ)) + δ)) hlarge_cover hbound
  have hnum : (large.card : ℝ) ≤ curves.card := by exact_mod_cast card_filter_le _ _
  have hcount' := hcount.trans (mul_le_mul_of_nonneg_right hnum
    (mul_nonneg hA.le (Real.rpow_nonneg (Nat.cast_nonneg H) _)))
  have hpartition : (U.card : ℝ) ≤ (V.card : ℝ) + ((U \ V).card : ℝ) := by
    have hsub : U ⊆ V ∪ (U \ V) := by
      intro v hv
      by_cases hV : v ∈ V
      · exact mem_union_left _ hV
      · exact mem_union_right _ (mem_sdiff.mpr ⟨hv, hV⟩)
    exact_mod_cast (card_le_card hsub).trans (card_union_le V (U \ V))
  have hinj : Function.Injective (fun p : ℤ × ℤ ↦ SourceIntegerLift.point D p.1 p.2 (w p)) := by
    intro p q hpq
    have heq := congrArg (SourceIntegerPoints.host D hD) hpq
    simpa only [SourceIntegerPoints.host_point] using heq
  have hUcard : U.card = F.card := card_image_of_injective F hinj
  have hfinal := hpartition.trans (add_le_add (le_refl (V.card : ℝ)) hcount')
  simpa only [hUcard, mul_assoc] using hfinal

end PaperP1.SourceCurvePointCover
