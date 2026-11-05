module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.Push

/-! # Actual homogeneous interpolation on a finite normalized coordinate population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousFiniteInterpolation

open MvPolynomial Finset
open scoped Classical

theorem selector {F σ : Type*} [Field F] (S : Finset (σ → F)) (z : σ)
    (hnormal : ∀ w ∈ S, w z = 1) (p : σ → F) (hp : p ∈ S)
    (n : ℕ) (hn : S.card - 1 ≤ n) :
    ∃ q : MvPolynomial σ F, q.IsHomogeneous n ∧
      ∀ w ∈ S, eval w q = if w = p then 1 else 0 := by
  classical
  let T := S.erase p
  have hsep (w : T) : ∃ i : σ, p i ≠ w.val i := by
    by_contra! hh
    exact (Finset.mem_erase.mp w.property).1 (funext hh).symm
  choose j hj using hsep
  let L : T → MvPolynomial σ F := fun w ↦
    C ((p (j w) - w.val (j w))⁻¹) * (X (j w) - C (w.val (j w)) * X z)
  have hLhom (w : T) : (L w).IsHomogeneous 1 :=
    ((isHomogeneous_X F (j w)).sub (isHomogeneous_C_mul_X _ z)).C_mul _
  have hLp (w : T) : eval p (L w) = 1 := by
    simp only [L, map_mul, eval_C, map_sub, eval_X, hnormal p hp, mul_one]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (hj w))
  have hLzero (w : T) : eval w.val (L w) = 0 := by
    have hwn := hnormal w.val (Finset.mem_of_mem_erase w.property)
    simp only [L, map_mul, eval_C, map_sub, eval_X, hwn, mul_one, sub_self, mul_zero]
  let r : MvPolynomial σ F := ∏ w : T, L w
  have hrhom : r.IsHomogeneous T.card := by
    have hh := IsHomogeneous.prod Finset.univ L (fun _ ↦ 1) (fun w _ ↦ hLhom w)
    simpa [r] using hh
  have hrp : eval p r = 1 := by simp only [r, map_prod, hLp, Finset.prod_const_one]
  have hrzero (w : σ → F) (hw : w ∈ T) : eval w r = 0 := by
    change eval w (∏ v : T, L v) = 0
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨w, hw⟩ : T)) (hLzero ⟨w, hw⟩)
  have hTn : T.card ≤ n := by
    have hc : T.card = S.card - 1 := Finset.card_erase_of_mem hp
    omega
  let q : MvPolynomial σ F := r * X z ^ (n - T.card)
  have hpow : (X z ^ (n - T.card) : MvPolynomial σ F).IsHomogeneous (n - T.card) := by
    simpa only [one_mul] using (isHomogeneous_X F z).pow (n - T.card)
  have hdegree : T.card + (n - T.card) = n := by omega
  refine ⟨q, by simpa only [hdegree] using hrhom.mul hpow, ?_⟩
  intro w hw
  have hqe : eval w q = eval w r := by simp only [q, map_mul, map_pow, eval_X, hnormal w hw, one_pow, mul_one]
  rw [hqe]
  by_cases hwp : w = p
  · rw [hwp, ite_eq_left rfl]
    exact hrp
  · rw [ite_eq_right hwp]
    exact hrzero w (Finset.mem_erase.mpr ⟨hwp, hw⟩)

end PaperP1.HomogeneousFiniteInterpolation
