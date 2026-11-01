module

public import PaperP1.Diophantine.HomogeneousCharts
public import PaperP1.Diophantine.SingleResultantFibreCount

/-! # Actual homogeneous auxiliary equations, without chart nondegeneracy assumptions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectiveCurveCount

open Finset MvPolynomial PaperP1.BidegreeOneFibreCount PaperP1.HomogeneousCharts

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def Good {ell : ℕ} (C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ)
    (F G : MvPolynomial (Fin 2) ℤ) (h : ℤ) (s : Point) : Prop :=
  (s.1 0).natAbs.Coprime (s.1 1).natAbs ∧
    (s.2 0).natAbs.Coprime (s.2 1).natAbs ∧
      s.1 0 * eval s.2 F + s.1 1 * eval s.2 G = 0 ∧
        PaperP1.BidegreeOneElimination.original C s.1 s.2 = h

def realSolutions {ell : ℕ} (C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ)
    (F G : MvPolynomial (Fin 2) ℤ) (h : ℤ) (A H : ℝ) : Finset Point :=
  ((Fintype.piFinset fun _ : Fin 2 ↦ Finset.Icc (-(⌊A⌋₊ : ℤ)) ⌊A⌋₊) ×ˢ
    (Fintype.piFinset fun _ : Fin 2 ↦ Finset.Icc (-(⌊H⌋₊ : ℤ)) ⌊H⌋₊)).filter (Good C F G h)

theorem good_eq_charts {ell d : ℕ} (C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ)
    (F G : MvPolynomial (Fin 2) ℤ) (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous d)
    (h : ℤ) (s : Point) :
    Good C F G h s ↔ PaperP1.BidegreeOneFibreCount.Good C (chart F) (chart G) d h s := by
  simp only [Good, PaperP1.BidegreeOneFibreCount.Good, chart_homogenize F hF,
    chart_homogenize G hG]

theorem realSolutions_eq_charts {ell d : ℕ} (C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ)
    (F G : MvPolynomial (Fin 2) ℤ) (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous d)
    (h : ℤ) (A H : ℝ) :
    realSolutions C F G h A H =
      PaperP1.BidegreeOneCurveCount.realSolutions C (chart F) (chart G) d h A H := by
  ext s
  simp only [realSolutions, PaperP1.BidegreeOneCurveCount.realSolutions,
    PaperP1.BidegreeOneCurveCount.solutions, mem_filter, good_eq_charts C F G hF hG]

theorem mem_realSolutions {ell : ℕ} (C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ)
    (F G : MvPolynomial (Fin 2) ℤ) (h : ℤ) (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) (s : Point) :
    s ∈ realSolutions C F G h A H ↔
      (∀ i, |(s.1 i : ℝ)| ≤ A) ∧ (∀ i, |(s.2 i : ℝ)| ≤ H) ∧ Good C F G h s := by
  simp only [realSolutions, mem_filter, mem_product, Fintype.mem_piFinset,
    PaperP1.BidegreeOneCurveCount.integer_box_floor _ A hA,
    PaperP1.BidegreeOneCurveCount.integer_box_floor _ H hH, and_assoc]

theorem homogeneous_relprime_count (ell k d : ℕ) (A₀ : ℝ) (hd : 0 < d)
    (hdegree : 0 < k + d * ell) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ F G : MvPolynomial (Fin 2) ℤ,
      F.IsHomogeneous d → G.IsHomogeneous d →
      IsRelPrime (MvPolynomial.map (Int.castRingHom ℚ) F)
        (MvPolynomial.map (Int.castRingHom ℚ) G) →
      (∀ m, ((F.coeff m).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) →
      (∀ m, ((G.coeff m).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) →
        ∀ C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ, (∀ i, (C i).IsHomogeneous k) →
          ∀ h : ℤ, h ≠ 0 → ∀ A H : ℝ, 0 ≤ A → 1 ≤ H →
            ((realSolutions C F G h A H).card : ℝ) ≤ (N : ℝ) ^ ε * H := by
  obtain ⟨N₀, hN₀⟩ := PaperP1.SingleResultantFibreCount.actual_real_solutions_count ell k d A₀ hd hdegree ε hε
  refine ⟨N₀, ?_⟩
  intro N hN F G hF hG hcop hfc hgc C hC h hh A H hA hH
  rw [realSolutions_eq_charts C F G hF hG]
  exact hN₀ N hN (chart F) (chart G) (chart_degree F hF) (chart_degree G hG)
    (integer_resultant_ne_zero F G d hd hF hG hcop)
    (chart_coefficient_bound F hF _ (Real.rpow_nonneg (Nat.cast_nonneg N) _) hfc)
    (chart_coefficient_bound G hG _ (Real.rpow_nonneg (Nat.cast_nonneg N) _) hgc)
    C hC h hh A H hA hH

theorem irreducible_auxiliary_count (ell k d : ℕ) (A₀ : ℝ) (hd : 0 < d)
    (hdegree : 0 < k + d * ell) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ F G : MvPolynomial (Fin 2) ℤ,
      F.IsHomogeneous d → G.IsHomogeneous d →
      Irreducible (MvPolynomial.C (MvPolynomial.map (Int.castRingHom ℚ) F) * MvPolynomial.X (0 : Fin 2) +
        MvPolynomial.C (MvPolynomial.map (Int.castRingHom ℚ) G) * MvPolynomial.X 1) →
      (∀ m, ((F.coeff m).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) →
      (∀ m, ((G.coeff m).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) →
        ∀ C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ, (∀ i, (C i).IsHomogeneous k) →
          ∀ h : ℤ, h ≠ 0 → ∀ A H : ℝ, 0 ≤ A → 1 ≤ H →
            ((realSolutions C F G h A H).card : ℝ) ≤ (N : ℝ) ^ ε * H := by
  obtain ⟨N₀, hN₀⟩ := homogeneous_relprime_count ell k d A₀ hd hdegree ε hε
  refine ⟨N₀, ?_⟩
  intro N hN F G hF hG hirr hfc hgc C hC h hh A H hA hH
  exact hN₀ N hN F G hF hG
    (PaperP1.ProjectiveResultants.coefficients_relprime_of_irreducible _ _ hirr)
    hfc hgc C hC h hh A H hA hH

end PaperP1.ProjectiveCurveCount
