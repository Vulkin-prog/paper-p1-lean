module

public import PaperP1.Algebra.BivariateRationalLines
public import PaperP1.Arithmetic.PlaneCurvePointCount
public import PaperP1.Combinatorics.FiniteCoverCount

/-! # Count all indexed offset points through actual irreducible polynomial factors

Only nonlinear irreducible curves use the curve-count argument. Actual collinear
subfamilies bound both line components and the multiplicity of a single point.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialOffsetPopulation

open Finset Polynomial PaperP1.BivariateFactorDegree UniqueFactorizationMonoid

theorem finite_bound {ι : Type*} (S : Finset ι) (s t : ι → ℤ) (P : ℚ[X][X])
    (B D : ℕ) (K F : ℝ) (hK : 0 ≤ K) (hF : 1 ≤ F)
    (hP : P ≠ 0) (hD : degreeSum P ≤ D)
    (hs : ∀ i ∈ S, (s i).natAbs ≤ B) (ht : ∀ i ∈ S, (t i).natAbs ≤ B)
    (hz : ∀ i ∈ S, P.evalEval (s i : ℚ) (t i : ℚ) = 0)
    (hlines : ∀ T : Finset ι, T ⊆ S →
      (∀ i ∈ T, ∀ j ∈ T, ∀ k ∈ T,
        (s j - s i) * (t k - t i) = (t j - t i) * (s k - s i)) →
        (T.card : ℝ) ≤ K)
    (hcurves : ∀ Q : ℚ[X][X], Irreducible Q → 2 ≤ totalDegree Q → degreeSum Q ≤ D →
      ((PlaneCurvePointCount.grid Q B).card : ℝ) ≤ F) :
    (S.card : ℝ) ≤ (D : ℝ) * K * F := by
  classical
  let : NormalizationMonoid ℚ[X][X] := Classical.choice inferInstance
  let I := (normalizedFactors P).toFinset
  let onCurve (Q : ℚ[X][X]) := S.filter fun i ↦ Q.evalEval (s i : ℚ) (t i : ℚ) = 0
  have hfactors := normalized_factor_bounds P hP
  have hI : I.card ≤ D := (Multiset.toFinset_card_le _).trans (hfactors.1.trans hD)
  have hcover (i : ι) (hi : i ∈ S) : ∃ Q ∈ I, i ∈ onCurve Q := by
    obtain ⟨Q, hQ, he⟩ := zero_on_factor P hP (s i : ℚ) (t i : ℚ) (hz i hi)
    exact ⟨Q, Multiset.mem_toFinset.mpr hQ, mem_filter.mpr ⟨hi, he⟩⟩
  have hone (Q : ℚ[X][X]) (hQI : Q ∈ I) : ((onCurve Q).card : ℝ) ≤ K * F := by
    obtain ⟨hirr, hdegree⟩ := hfactors.2 Q (Multiset.mem_toFinset.mp hQI)
    have hpos := irreducible_totalDegree_pos Q hirr
    by_cases hlinear : totalDegree Q = 1
    · have hcol : ∀ i ∈ onCurve Q, ∀ j ∈ onCurve Q, ∀ k ∈ onCurve Q,
          (s j - s i) * (t k - t i) = (t j - t i) * (s k - s i) := by
        intro i hi j hj k hk
        exact BivariateRationalLines.integer_points_cross Q hlinear (s i, t i) (s j, t j) (s k, t k)
          (mem_filter.mp hi).2 (mem_filter.mp hj).2 (mem_filter.mp hk).2
      have hh := hlines (onCurve Q) (filter_subset _ _) hcol
      exact hh.trans (by nlinarith only [hF, hK])
    · let fibre (v : ℤ × ℤ) := (onCurve Q).filter fun i ↦ (s i, t i) = v
      have hfibre (v : ℤ × ℤ) (_hv : v ∈ PlaneCurvePointCount.grid Q B) :
          ((fibre v).card : ℝ) ≤ K := by
        apply hlines (fibre v) ((filter_subset _ _).trans (filter_subset _ _))
        intro i hi j hj k hk
        have hei := (mem_filter.mp hi).2
        have hej := (mem_filter.mp hj).2
        have hek := (mem_filter.mp hk).2
        have hsji : s j = s i := congrArg Prod.fst (hej.trans hei.symm)
        have htji : t j = t i := congrArg Prod.snd (hej.trans hei.symm)
        rw [hsji, htji, sub_self, sub_self, zero_mul, zero_mul]
      have hfcover (i : ι) (hi : i ∈ onCurve Q) :
          ∃ v ∈ PlaneCurvePointCount.grid Q B, i ∈ fibre v := by
        have hiS := (mem_filter.mp hi).1
        refine ⟨(s i, t i), (PlaneCurvePointCount.mem_grid Q B _).mpr ?_, mem_filter.mpr ⟨hi, rfl⟩⟩
        refine ⟨?_, ?_, (mem_filter.mp hi).2⟩
        · rw [Int.abs_eq_natAbs]
          exact_mod_cast hs i hiS
        · rw [Int.abs_eq_natAbs]
          exact_mod_cast ht i hiS
      have hh := FiniteCoverCount.cardinal_le (onCurve Q) (PlaneCurvePointCount.grid Q B) fibre K hfcover hfibre
      have hg := hcurves Q hirr (by omega) (hdegree.trans hD)
      calc
        _ ≤ ((PlaneCurvePointCount.grid Q B).card : ℝ) * K := hh
        _ ≤ F * K := mul_le_mul_of_nonneg_right hg hK
        _ = _ := mul_comm _ _
  have hall := FiniteCoverCount.cardinal_le S I onCurve (K * F) hcover hone
  calc
    _ ≤ (I.card : ℝ) * (K * F) := hall
    _ ≤ (D : ℝ) * (K * F) := mul_le_mul_of_nonneg_right (by exact_mod_cast hI) (by positivity)
    _ = _ := by ring

end PaperP1.PolynomialOffsetPopulation
