module

public import PaperP1.Algebra.IrreducibleHomogenization
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Bivariate

/-! # Exact two-step bivariate homogenization and its irreducibility -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateIrreducibleHomogenization

open Polynomial Finset

variable {R : Type*} [CommRing R]

theorem comm_coefficient {σ τ : Type*}
    (P : MvPolynomial σ (MvPolynomial τ R)) (m : τ →₀ ℕ) (n : σ →₀ ℕ) :
    ((MvPolynomial.commAlgEquiv R σ τ P).coeff m).coeff n = (P.coeff n).coeff m := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP, hQ]
  | monomial i p =>
    induction p using MvPolynomial.induction_on' with
    | add p q hp hq =>
      simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
    | monomial j r =>
      have he : MvPolynomial.commAlgEquiv R σ τ
          (MvPolynomial.monomial i (MvPolynomial.monomial j r)) =
          MvPolynomial.monomial j (MvPolynomial.monomial i r) :=
        AddMonoidAlgebra.commAlgEquiv_single_single i j r
      rw [he]
      by_cases hi : i = n <;> by_cases hj : j = m <;> simp [hi, hj]

variable (R) in
def reorder : MvPolynomial (Fin 2) R[X] ≃ₐ[R] (MvPolynomial (Fin 2) R)[X] :=
  (MvPolynomial.mapAlgEquiv (σ := Fin 2) (MvPolynomial.uniqueAlgEquiv R Unit).symm).trans
    ((MvPolynomial.commAlgEquiv R (Fin 2) Unit).trans
      ((MvPolynomial.uniqueAlgEquiv (MvPolynomial (Fin 2) R) Unit).restrictScalars R))

theorem reorder_coefficient (F : MvPolynomial (Fin 2) R[X]) (i : ℕ) (m : Fin 2 →₀ ℕ) :
    ((reorder R F).coeff i).coeff m = (F.coeff m).coeff i := by
  change (((MvPolynomial.uniqueAlgEquiv (MvPolynomial (Fin 2) R) Unit)
    ((MvPolynomial.commAlgEquiv R (Fin 2) Unit)
      (MvPolynomial.map (MvPolynomial.uniqueAlgEquiv R Unit).symm.toRingHom F))).coeff i).coeff m = _
  rw [MvPolynomial.coeff_uniqueAlgEquiv, comm_coefficient, MvPolynomial.coeff_map]
  change (((MvPolynomial.uniqueAlgEquiv R Unit).symm (F.coeff m)).coeff
    (Finsupp.single (default : Unit) i)) = _
  rw [MvPolynomial.coeff_uniqueAlgEquiv_symm, Finsupp.single_eq_same]

theorem reorder_homogenize_coefficient (P : R[X][X]) (b i : ℕ) (m : Fin 2 →₀ ℕ) :
    ((reorder R (P.homogenize b)).coeff i).coeff m =
      if m 0 + m 1 = b then (P.coeff (m 0)).coeff i else 0 := by
  rw [reorder_coefficient, Polynomial.coeff_homogenize]
  by_cases hm : m 0 + m 1 = b <;> simp [hm]

theorem swap_coefficient (P : R[X][X]) (i j : ℕ) :
    ((Bivariate.swap P).coeff j).coeff i = (P.coeff i).coeff j := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, coeff_add, hP, hQ]
  | monomial n p =>
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, coeff_add, hp, hq]
    | monomial m a =>
      rw [Bivariate.swap_monomial_monomial]
      by_cases hn : n = i <;> by_cases hm : m = j <;> simp [coeff_monomial, hn, hm]

theorem coefficient_degree_le (P : R[X][X]) (i : ℕ) :
    (P.coeff i).natDegree ≤ (Bivariate.swap P).natDegree := by
  by_cases hp : P.coeff i = 0
  · simp only [hp, natDegree_zero]
    exact Nat.zero_le _
  · have hc : (P.coeff i).coeff (P.coeff i).natDegree ≠ 0 := by
      rw [coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr hp
    have hs : (Bivariate.swap P).coeff (P.coeff i).natDegree ≠ 0 := by
      intro hz
      apply hc
      rw [← swap_coefficient, hz, coeff_zero]
    exact le_natDegree_of_ne_zero hs

theorem reorder_homogenize_degree (P : R[X][X]) (hP : P ≠ 0) :
    (reorder R (P.homogenize P.natDegree)).natDegree = (Bivariate.swap P).natDegree := by
  classical
  let a := (Bivariate.swap P).natDegree
  let b := P.natDegree
  change (reorder R (P.homogenize b)).natDegree = a
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    apply MvPolynomial.ext
    intro m
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    rw [reorder_homogenize_coefficient]
    by_cases hm : m 0 + m 1 = b
    · rw [ite_eq_left hm]
      exact coeff_eq_zero_of_natDegree_lt ((coefficient_degree_le P (m 0)).trans_lt hi)
    · exact ite_eq_right hm
  · have hswap : Bivariate.swap P ≠ 0 := by
      intro hz
      apply hP
      exact (Bivariate.swap (R := R)).injective (hz.trans (map_zero (Bivariate.swap (R := R))).symm)
    have hrow : (Bivariate.swap P).coeff a ≠ 0 := by
      simpa only [a, coeff_natDegree] using leadingCoeff_ne_zero.mpr hswap
    let j := ((Bivariate.swap P).coeff a).natDegree
    have hj : ((Bivariate.swap P).coeff a).coeff j ≠ 0 := by
      simpa only [j, coeff_natDegree] using leadingCoeff_ne_zero.mpr hrow
    have hpcoeff : (P.coeff j).coeff a ≠ 0 := by
      rw [← swap_coefficient P j a]
      exact hj
    have hPj : P.coeff j ≠ 0 := by
      intro hz
      exact hpcoeff (by rw [hz, coeff_zero])
    have hj_le : j ≤ b := le_natDegree_of_ne_zero hPj
    have hT : ((reorder R (P.homogenize b)).coeff a).coeff
        (fun₀ | 0 => j | 1 => b - j) ≠ 0 := by
      rw [reorder_homogenize_coefficient]
      simpa [Nat.add_sub_of_le hj_le] using hpcoeff
    have hTne : (reorder R (P.homogenize b)).coeff a ≠ 0 := by
      intro hz
      apply hT
      rw [hz]
      rfl
    exact le_natDegree_of_ne_zero hTne

def bihomogenize (P : R[X][X]) : MvPolynomial (Fin 2) (MvPolynomial (Fin 2) R) :=
  (reorder R (P.homogenize P.natDegree)).homogenize (Bivariate.swap P).natDegree

theorem bihomogenize_coefficient (P : R[X][X]) (m n : Fin 2 →₀ ℕ) :
    ((bihomogenize P).coeff m).coeff n =
      if m 0 + m 1 = (Bivariate.swap P).natDegree ∧ n 0 + n 1 = P.natDegree
        then (P.coeff (n 0)).coeff (m 0) else 0 := by
  unfold bihomogenize
  rw [Polynomial.coeff_homogenize]
  by_cases hm : m 0 + m 1 = (Bivariate.swap P).natDegree
  · rw [ite_eq_left hm, reorder_homogenize_coefficient]
    simp only [hm, true_and]
  · simp [hm]

variable [IsDomain R]

theorem bihomogenize_irreducible (P : R[X][X]) (hP : Irreducible P) :
    Irreducible (bihomogenize P) := by
  have h₁ := PaperP1.IrreducibleHomogenization.homogenize_irreducible P hP
  have h₂ : Irreducible (reorder R (P.homogenize P.natDegree)) :=
    (MulEquiv.irreducible_iff (reorder R)).mpr h₁
  have h₃ := PaperP1.IrreducibleHomogenization.homogenize_irreducible
    (reorder R (P.homogenize P.natDegree)) h₂
  simpa only [bihomogenize, reorder_homogenize_degree P hP.ne_zero] using h₃

end PaperP1.BivariateIrreducibleHomogenization
