module

public import PaperP1.Diophantine.PrimitiveDirections

/-! # Height-independent primitive zeros of a nonzero homogeneous binary form -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveHomogeneousZeros

open Finset Polynomial PaperP1.HomogeneousCharts PaperP1.PrimitiveDirections

theorem chart_ne_zero (F : MvPolynomial (Fin 2) ℤ) {d : ℕ}
    (hF : F.IsHomogeneous d) (hF0 : F ≠ 0) : chart F ≠ 0 := by
  intro hp
  have h := chart_homogenize F hF
  rw [hp, Polynomial.homogenize_zero] at h
  exact hF0 h.symm

theorem ratio_is_root (F : MvPolynomial (Fin 2) ℤ) {d : ℕ}
    (hF : F.IsHomogeneous d) (z : Pair) (hz : z 1 ≠ 0)
    (heval : MvPolynomial.eval z F = 0) :
    ((chart F).map (Int.castRingHom ℚ)).IsRoot (ratio z) := by
  let φ := Int.castRingHom ℚ
  let zQ : Fin 2 → ℚ := fun i ↦ φ (z i)
  have hb : zQ 1 ≠ 0 := by dsimp [zQ, φ]; exact_mod_cast hz
  have hcast : MvPolynomial.eval zQ (MvPolynomial.map φ F) = 0 := by
    calc
      _ = φ (MvPolynomial.eval z F) := by
        rw [MvPolynomial.eval_map]
        exact (MvPolynomial.hom_eval₂ F (RingHom.id ℤ) φ z).symm
      _ = 0 := by rw [heval, map_zero]
  have hdegree : ((chart F).map φ).natDegree ≤ d :=
    (Polynomial.natDegree_map_le).trans (chart_degree F hF)
  have hhom : ((chart F).map φ).homogenize d = MvPolynomial.map φ F := by
    rw [Polynomial.homogenize_map, chart_homogenize F hF]
  have hzero : MvPolynomial.eval zQ (((chart F).map φ).homogenize d) = 0 := by
    rw [hhom]
    exact hcast
  rw [Polynomial.eval_homogenize hdegree zQ hb] at hzero
  exact (mul_eq_zero.mp hzero).resolve_right (pow_ne_zero _ hb)

theorem nonaxis_card (F : MvPolynomial (Fin 2) ℤ) {d : ℕ}
    (hF : F.IsHomogeneous d) (hF0 : F ≠ 0) (S : Finset Pair)
    (hprimitive : ∀ z ∈ S, (z 0).natAbs.Coprime (z 1).natAbs)
    (hden : ∀ z ∈ S, z 1 ≠ 0) (hzero : ∀ z ∈ S, MvPolynomial.eval z F = 0) :
    S.card ≤ 2 * d := by
  classical
  let p := (chart F).map (Int.castRingHom ℚ)
  have hp : p ≠ 0 := (Polynomial.map_ne_zero_iff (by exact Int.cast_injective)).mpr (chart_ne_zero F hF hF0)
  have hmem : ∀ z ∈ S, ratio z ∈ p.roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
    exact ratio_is_root F hF z (hden z hz) (hzero z hz)
  have hcount : S.card ≤ 2 * p.roots.toFinset.card :=
    Finset.card_le_mul_card_image_of_maps_to hmem 2 (fun r _ ↦ ratio_fibre_card S hprimitive hden r)
  have hroots : p.roots.toFinset.card ≤ d :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' p).trans
      (Polynomial.natDegree_map_le.trans (chart_degree F hF)))
  exact hcount.trans (Nat.mul_le_mul_left 2 hroots)

theorem primitive_card (F : MvPolynomial (Fin 2) ℤ) {d : ℕ}
    (hF : F.IsHomogeneous d) (hF0 : F ≠ 0) (S : Finset Pair)
    (hprimitive : ∀ z ∈ S, (z 0).natAbs.Coprime (z 1).natAbs)
    (hzero : ∀ z ∈ S, MvPolynomial.eval z F = 0) : S.card ≤ 2 * (d + 1) := by
  classical
  have hn := nonaxis_card F hF hF0 (S.filter fun z ↦ z 1 ≠ 0)
    (fun z hz ↦ hprimitive z (mem_filter.mp hz).1)
    (fun _ hz ↦ (mem_filter.mp hz).2) (fun z hz ↦ hzero z (mem_filter.mp hz).1)
  have ha := axis_card (S.filter fun z ↦ z 1 = 0)
    (fun z hz ↦ hprimitive z (mem_filter.mp hz).1) (fun _ hz ↦ (mem_filter.mp hz).2)
  have hpartition := Finset.card_filter_add_card_filter_not (s := S) (fun z : Pair ↦ z 1 ≠ 0)
  simp only [not_not] at hpartition
  omega

end PaperP1.PrimitiveHomogeneousZeros
