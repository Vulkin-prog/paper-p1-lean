module

public import PaperP1.Algebra.WeightedMonomialOrder
public import PaperP1.Algebra.NormalizedP3MonomialHeight
public import PaperP1.Geometry.P3HypersurfaceRationalData
public import PaperP1.Arithmetic.UniformP3HypersurfaceCover
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Tactic.Push

/-! # The actual leading monomial avoids the fixed chart coordinate unless the chart population is empty -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3HeightLeadingMonomial

open MvPolynomial

def heightWeight : Fin 4 → ℕ := Fin.snoc (fun _ : Fin 3 ↦ 1) 0

def order : MonomialOrder (Fin 4) := WeightedMonomialOrder.order heightWeight

theorem weight_eq_freeDegree (m : Fin 4 →₀ ℕ) :
    Finsupp.weight heightWeight m = NormalizedP3MonomialHeight.freeDegree m := by
  rw [Finsupp.weight_eq_sum, Fin.sum_univ_castSucc]
  rw [show heightWeight (Fin.last 3) = 0 from Fin.snoc_last _ _]
  simp [heightWeight, NormalizedP3MonomialHeight.freeDegree]

theorem exists_normalizer_free_support {R : Type*} [CommSemiring R]
    (q : MvPolynomial (Fin 4) R) (hnot : ¬ X (3 : Fin 4) ∣ q) :
    ∃ r ∈ q.support, r 3 = 0 := by
  classical
  by_contra hn
  push Not at hn
  apply hnot
  rw [← q.support_sum_monomial_coeff]
  apply Finset.dvd_sum
  intro r hr
  exact X_dvd_monomial.mpr (Or.inr (hn r hr))

theorem leading_degree {R : Type*} [CommSemiring R] (d : ℕ) (q : MvPolynomial (Fin 4) R)
    (hq : q.IsHomogeneous d) (hq0 : q ≠ 0) : (order.degree q).degree = d := by
  have he := hq.degree_eq_sum_deg_support (order.degree_mem_support hq0)
  simpa only [Finsupp.degree_apply] using he.symm

theorem leading_freeDegree {R : Type*} [CommSemiring R] (d : ℕ) (q : MvPolynomial (Fin 4) R)
    (hq : q.IsHomogeneous d) (hq0 : q ≠ 0) (hnot : ¬ X (3 : Fin 4) ∣ q) :
    NormalizedP3MonomialHeight.freeDegree (order.degree q) = d := by
  obtain ⟨r, hr, hr3⟩ := exists_normalizer_free_support q hnot
  have he := hq.degree_eq_sum_deg_support hr
  have hrdeg : r.degree = d := by simpa only [Finsupp.degree_apply] using he.symm
  have hweight := WeightedMonomialOrder.leading_weight_ge heightWeight q r hr
  rw [weight_eq_freeDegree, weight_eq_freeDegree] at hweight
  change NormalizedP3MonomialHeight.freeDegree r ≤
    NormalizedP3MonomialHeight.freeDegree (order.degree q) at hweight
  have hs := NormalizedP3MonomialHeight.degree_split r
  have hl := NormalizedP3MonomialHeight.degree_split (order.degree q)
  have hld := leading_degree d q hq hq0
  omega

theorem leading_normalizer_zero {R : Type*} [CommSemiring R] (d : ℕ) (q : MvPolynomial (Fin 4) R)
    (hq : q.IsHomogeneous d) (hq0 : q ≠ 0) (hnot : ¬ X (3 : Fin 4) ∣ q) :
    order.degree q 3 = 0 := by
  have hf := leading_freeDegree d q hq hq0 hnot
  have hd := leading_degree d q hq hq0
  have hs := NormalizedP3MonomialHeight.degree_split (order.degree q)
  omega

theorem points_empty_of_dvd_coordinate (q : MvPolynomial (Fin 4) ℚ)
    (hdiv : q ∣ X (3 : Fin 4)) (H : ℕ) : UniformP3HypersurfaceCover.points q H = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro v hv
  have hpoint := (UniformP3HypersurfaceCover.mem_points q H v).mp hv
  have hd := map_dvd (eval (fun i ↦ (v i : ℚ))) hdiv
  rw [hpoint.2.2, eval_X, hpoint.2.1, Int.cast_one] at hd
  exact one_ne_zero (zero_dvd_iff.mp hd)

theorem leading_or_empty (d : ℕ) (q : MvPolynomial (Fin 4) ℚ)
    (hgeom : Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) q)) (hq : q.IsHomogeneous d) :
    (∀ H, UniformP3HypersurfaceCover.points q H = ∅) ∨
      order.degree q 3 = 0 ∧ (order.degree q).degree = d := by
  have hirr := P3HypersurfaceRationalData.irreducible q hgeom
  by_cases hx : X (3 : Fin 4) ∣ q
  · have hX : Irreducible (X (3 : Fin 4) : MvPolynomial (Fin 4) ℚ) := (prime_X (i := (3 : Fin 4))).irreducible
    have hqX : q ∣ X (3 : Fin 4) := (hX.associated_of_dvd hirr hx).symm.dvd
    exact Or.inl (points_empty_of_dvd_coordinate q hqX)
  · exact Or.inr ⟨leading_normalizer_zero d q hq hirr.ne_zero hx, leading_degree d q hq hirr.ne_zero⟩

end PaperP1.P3HeightLeadingMonomial
