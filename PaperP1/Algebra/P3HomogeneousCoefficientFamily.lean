module

public import PaperP1.Algebra.HomogeneousMonomialCount
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

/-! # Literal coefficient families for homogeneous four-coordinate polynomials -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3HomogeneousCoefficientFamily

open MvPolynomial Finset

abbrev Index (d : ℕ) := {m : Fin 4 →₀ ℕ // m.degree = d}

instance indexFinite (d : ℕ) : Finite (Index d) :=
  HomogeneousMonomialCount.exponent_finite (Fin 4) d

instance indexFintype (d : ℕ) : Fintype (Index d) := Fintype.ofFinite (Index d)

theorem index_card (d : ℕ) : Fintype.card (Index d) = (d + 3).choose 3 := by
  have hc := HomogeneousMonomialCount.exponent_card (Fin 4) d
  rw [Nat.card_fin, show 4 + d - 1 = d + 3 by omega, Nat.choose_symm_add] at hc
  simpa only [Nat.card_eq_fintype_card] using hc

variable {R : Type*} [CommRing R]

def polynomial (d : ℕ) (w : Index d → R) : MvPolynomial (Fin 4) R :=
  ∑ m, monomial m.val (w m)

theorem coeff_index (d : ℕ) (w : Index d → R) (m : Index d) :
    (polynomial d w).coeff m.val = w m := by
  classical
  simp [polynomial, Subtype.val_injective.eq_iff]

theorem coeff_outside (d : ℕ) (w : Index d → R) (m : Fin 4 →₀ ℕ) (hm : m.degree ≠ d) :
    (polynomial d w).coeff m = 0 := by
  classical
  have hne (s : Index d) : s.val ≠ m := by
    intro he
    exact hm (he ▸ s.property)
  simp only [polynomial, coeff_sum, coeff_monomial, ite_eq_right (hne _), sum_const_zero]

theorem homogeneous (d : ℕ) (w : Index d → R) : (polynomial d w).IsHomogeneous d := by
  apply IsHomogeneous.sum
  intro m _hm
  exact isHomogeneous_monomial (w m) m.property

theorem reconstruct (d : ℕ) (P : MvPolynomial (Fin 4) R) (hP : P.IsHomogeneous d) :
    polynomial d (fun m ↦ P.coeff m.val) = P := by
  classical
  ext m
  by_cases hm : m.degree = d
  · exact coeff_index d (fun m ↦ P.coeff m.val) ⟨m, hm⟩
  · rw [coeff_outside d _ m hm]
    apply Eq.symm
    by_contra hc
    apply hm
    have he := hP.degree_eq_sum_deg_support (mem_support_iff.mpr hc)
    simpa only [Finsupp.degree_apply] using he.symm

theorem nonzero (d : ℕ) (w : Index d → R) (hw : w ≠ 0) : polynomial d w ≠ 0 := by
  intro hz
  apply hw
  funext m
  have he := congrArg (fun P : MvPolynomial (Fin 4) R ↦ P.coeff m.val) hz
  simpa [coeff_index] using he

theorem evaluation (d : ℕ) (w : Index d → R) (v : Fin 4 → R) :
    eval v (polynomial d w) = ∑ m, m.val.prod (fun i e ↦ v i ^ e) * w m := by
  classical
  rw [polynomial, map_sum]
  apply sum_congr rfl
  intro m _hm
  rw [eval_monomial, mul_comm]

end PaperP1.P3HomogeneousCoefficientFamily
