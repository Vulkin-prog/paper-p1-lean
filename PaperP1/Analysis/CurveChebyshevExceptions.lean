module

public import PaperP1.Algebra.PlaneSingularPoints
public import PaperP1.Analysis.NonsingularMonomialPieces

/-! # Complete real singular and monomial Wronskian exceptions

The finite set is controlled even when the curve has no real regular point.
Every point outside it has an actual local simultaneous counting piece.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurveChebyshevExceptions

open MvPolynomial Set Finset MonomialWronskianExceptions NonstationaryTangentImage
  PolynomialTangentTrajectory TotalDegreeMonomials

def points (P : MvPolynomial (Fin 2) ℝ) (k : ℕ) : Set (Fin 2 → ℝ) :=
  PlaneSingularPoints.points P ∪ exceptionalPoints P k

theorem regular_and_avoids (P : MvPolynomial (Fin 2) ℝ) (k : ℕ) (z : Fin 2 → ℝ)
    (hzero : eval z P = 0) (hnot : z ∉ points P k) :
    (∃ i : Fin 2, eval z (pderiv i P) ≠ 0) ∧ z ∉ exceptionalPoints P k := by
  exact ⟨PlaneSingularPoints.gradient_nonzero_of_not_mem P z hzero (fun hz ↦ hnot (Or.inl hz)),
    fun hz ↦ hnot (Or.inr hz)⟩

theorem exists_finset (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (k : ℕ) (hk : k < P.totalDegree) :
    ∃ E : Finset (Fin 2 → ℝ), (∀ z, z ∈ E ↔ z ∈ points P k) ∧
      E.card ≤ 3 * P.totalDegree ^ 2 * (k + 1) ^ 6 := by
  classical
  obtain ⟨U, hU, hUcard⟩ := PlaneSingularPoints.exists_finset P hP (by omega)
  have hscale : P.totalDegree * (P.totalDegree - 1) ≤ P.totalDegree ^ 2 * (k + 1) ^ 6 := by
    calc
      _ ≤ P.totalDegree * P.totalDegree := Nat.mul_le_mul_left _ (Nat.sub_le _ 1)
      _ = P.totalDegree ^ 2 := (pow_two _).symm
      _ ≤ _ := by simpa only [mul_one] using
        Nat.mul_le_mul_left (P.totalDegree ^ 2) (Nat.one_le_pow 6 (k + 1) (by omega))
  by_cases hex : ∃ z : Fin 2 → ℝ, eval z P = 0 ∧ ∃ i : Fin 2, eval z (pderiv i P) ≠ 0
  · obtain ⟨z, hz, hgradient⟩ := hex
    obtain ⟨r, _h₀, _hpoint⟩ := LocalRegularTangentPiece.exists_piece_at_nonsingular P z hz hgradient
    obtain ⟨V, hV, hVcard⟩ := exists_exceptional_finset P hP k hk r
    refine ⟨U ∪ V, ?_, ?_⟩
    · intro z
      simp only [Finset.mem_union, hU z, hV z, points, Set.mem_union]
    · have hc := Finset.card_union_le U V
      nlinarith only [hc, hUcard, hVcard, hscale]
  · refine ⟨U, ?_, ?_⟩
    · intro z
      constructor
      · intro hz
        exact Or.inl ((hU z).mp hz)
      · intro hz
        rcases hz with hz | hz
        · exact (hU z).mpr hz
        · apply (hU z).mpr
          refine ⟨hz.1, ?_⟩
          intro i
          by_contra hi
          exact hex ⟨z, hz.1, i, hi⟩
    · nlinarith only [hUcard, hscale, Nat.zero_le (P.totalDegree ^ 2 * (k + 1) ^ 6)]

theorem exists_counting_piece (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (k : ℕ) (hk : k < P.totalDegree) (z : Fin 2 → ℝ) (hzero : eval z P = 0)
    (hnot : z ∉ points P k) :
    ∃ r : RegularPiece P, 0 ∈ Ioo r.left r.right ∧ position r.path 0 = z ∧
      (∀ t ∈ Ioo r.left r.right, position r.path t ∉ points P k) ∧
      ∀ Q : MvPolynomial (Fin 2) ℝ, Q ≠ 0 → Q.totalDegree ≤ k →
      ∀ S : Finset (Fin 2 → ℝ),
      (∀ w ∈ S, (∃ t ∈ Ioo r.left r.right, position r.path t = w) ∧ eval w Q = 0) →
        S.card < Fintype.card (Index k) := by
  obtain ⟨hgradient, havoid⟩ := regular_and_avoids P k z hzero hnot
  obtain ⟨r, h₀, hpoint, hnon, hcount⟩ :=
    NonsingularMonomialPieces.exists_counting_piece P hP k hk z hzero hgradient havoid
  refine ⟨r, h₀, hpoint, ?_, hcount⟩
  intro t ht hbad
  rcases hbad with hs | hw
  · obtain ⟨i, hi⟩ := r.nonstationary t ht
    exact hi (by simp [velocity, hs.2])
  · exact hnon t ht hw

end PaperP1.CurveChebyshevExceptions
