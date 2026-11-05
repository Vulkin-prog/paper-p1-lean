module

public import PaperP1.Analysis.LocalRegularTangentPiece
public import PaperP1.Analysis.MonomialCurvePieceCount

/-! # Actual local counting pieces through nonexceptional nonsingular points

The interval is constructed before every tested bounded-degree polynomial.
Its trajectory and avoidance properties are conclusions, not inputs.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonsingularMonomialPieces

open Set Filter MvPolynomial MonomialWronskianExceptions NonstationaryTangentImage
  PolynomialTangentTrajectory TotalDegreeMonomials
open scoped Topology

theorem exists_nonexceptional_piece (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (k : ℕ) (hk : k < P.totalDegree) (z : Fin 2 → ℝ) (hzero : eval z P = 0)
    (hgradient : ∃ i : Fin 2, eval z (pderiv i P) ≠ 0) (havoid : z ∉ exceptionalPoints P k) :
    ∃ r : RegularPiece P, 0 ∈ Ioo r.left r.right ∧ position r.path 0 = z ∧
      ∀ t ∈ Ioo r.left r.right, position r.path t ∉ exceptionalPoints P k := by
  classical
  obtain ⟨r, h₀, hpoint⟩ := LocalRegularTangentPiece.exists_piece_at_nonsingular P z hzero hgradient
  obtain ⟨E, hE, _hcard⟩ := exists_exceptional_finset P hP k hk r
  have hclosed : IsClosed (E : Set (Fin 2 → ℝ)) := E.finite_toSet.isClosed
  have hnot : z ∉ E := fun hz ↦ havoid ((hE z).mp hz)
  have hnot₀ : position r.path 0 ∈ (E : Set (Fin 2 → ℝ))ᶜ := by rw [hpoint]; exact hnot
  have hc : ContinuousAt (position r.path) 0 :=
    (continuousOn_position P r.path _ r.trajectory).continuousAt (isOpen_Ioo.mem_nhds h₀)
  have hn : {t : ℝ | position r.path t ∉ E} ∈ 𝓝 0 :=
    hc.tendsto.eventually (hclosed.isOpen_compl.mem_nhds hnot₀)
  have hnb : {t : ℝ | t ∈ Ioo r.left r.right ∧ position r.path t ∉ E} ∈ 𝓝 0 :=
    Filter.inter_mem (isOpen_Ioo.mem_nhds h₀) hn
  obtain ⟨a, b, h₀ab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnb
  let r' : RegularPiece P :=
    ⟨a, b, h₀ab.1.trans h₀ab.2, r.path, fun t ht ↦ r.trajectory t (hsub ht).1,
      fun t ht ↦ r.equation t (hsub ht).1, fun t ht ↦ r.nonstationary t (hsub ht).1⟩
  refine ⟨r', h₀ab, hpoint, ?_⟩
  intro t ht hz
  exact (hsub ht).2 ((hE _).mpr hz)

theorem exists_counting_piece (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (k : ℕ) (hk : k < P.totalDegree) (z : Fin 2 → ℝ) (hzero : eval z P = 0)
    (hgradient : ∃ i : Fin 2, eval z (pderiv i P) ≠ 0) (havoid : z ∉ exceptionalPoints P k) :
    ∃ r : RegularPiece P, 0 ∈ Ioo r.left r.right ∧ position r.path 0 = z ∧
      (∀ t ∈ Ioo r.left r.right, position r.path t ∉ exceptionalPoints P k) ∧
      ∀ Q : MvPolynomial (Fin 2) ℝ, Q ≠ 0 → Q.totalDegree ≤ k →
      ∀ S : Finset (Fin 2 → ℝ),
      (∀ w ∈ S, (∃ t ∈ Ioo r.left r.right, position r.path t = w) ∧ eval w Q = 0) →
        S.card < Fintype.card (Index k) := by
  obtain ⟨r, h₀, hpoint, hnon⟩ := exists_nonexceptional_piece P hP k hk z hzero hgradient havoid
  refine ⟨r, h₀, hpoint, hnon, ?_⟩
  intro Q hQ hdegree S hS
  exact MonomialCurvePieceCount.point_count P k r hnon Q hQ hdegree S hS

end PaperP1.NonsingularMonomialPieces
