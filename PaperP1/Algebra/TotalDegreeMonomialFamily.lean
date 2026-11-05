module

public import PaperP1.Algebra.TotalDegreeMonomials
public import PaperP1.Analysis.CurvePolynomialWronskianNonvanishing

/-! # Concrete independent real monomial families of bounded total degree

Any injective enumeration or initial subfamily retains coefficient recovery.
The number of monomials has the explicit quadratic upper bound.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TotalDegreeMonomialFamily

open MvPolynomial Finset TotalDegreeMonomials CurvePolynomialWronskianNonvanishing

def exponent {k : ℕ} (i : Index k) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i.val.1.val + Finsupp.single 1 i.val.2.val

def basis {k : ℕ} (i : Index k) : MvPolynomial (Fin 2) ℝ := monomial (exponent i) 1

theorem exponent_injective (k : ℕ) : Function.Injective (exponent (k := k)) := by
  intro i j he
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    have hh := congrArg (fun m : Fin 2 →₀ ℕ ↦ m 0) he
    simpa [exponent] using hh
  · apply Fin.ext
    have hh := congrArg (fun m : Fin 2 →₀ ℕ ↦ m 1) he
    simpa [exponent] using hh

theorem exponent_sum {k : ℕ} (i : Index k) :
    (exponent i).sum (fun _ e ↦ e) = i.val.1.val + i.val.2.val := by
  simp [exponent, Finsupp.sum_add_index']

theorem basis_degree {k : ℕ} (i : Index k) : (basis i).totalDegree ≤ k := by
  calc
    _ ≤ (exponent i).sum (fun _ e ↦ e) := totalDegree_monomial_le _ _
    _ = i.val.1.val + i.val.2.val := exponent_sum i
    _ ≤ k := i.property

theorem combination_coefficient (k n : ℕ) (e : Fin n → Index k) (he : Function.Injective e)
    (c : Fin n → ℝ) (i : Fin n) :
    (polynomialCombination (fun j ↦ basis (e j)) c).coeff (exponent (e i)) = c i := by
  classical
  simp only [polynomialCombination, coeff_sum, basis, C_mul_monomial, mul_one, coeff_monomial]
  have hiff (j : Fin n) : exponent (e j) = exponent (e i) ↔ j = i :=
    (exponent_injective k).eq_iff.trans he.eq_iff
  simp_rw [hiff]
  simp

theorem combination_ne_zero (k n : ℕ) (e : Fin n → Index k) (he : Function.Injective e)
    (c : Fin n → ℝ) (hc : c ≠ 0) : polynomialCombination (fun j ↦ basis (e j)) c ≠ 0 := by
  intro hz
  apply hc
  funext i
  have hh := congrArg (fun Q : MvPolynomial (Fin 2) ℝ ↦ Q.coeff (exponent (e i))) hz
  rw [combination_coefficient k n e he c i] at hh
  simpa using hh

theorem index_card_le (k : ℕ) : Fintype.card (Index k) ≤ (k + 1) ^ 2 := by
  have hh := Fintype.card_subtype_le (fun i : Fin (k + 1) × Fin (k + 1) ↦ i.1.val + i.2.val ≤ k)
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using hh

def enumeration (k : ℕ) : Fin (Fintype.card (Index k)) ≃ Index k := (Fintype.equivFin (Index k)).symm

def family (k : ℕ) : Fin (Fintype.card (Index k)) → MvPolynomial (Fin 2) ℝ :=
  fun i ↦ basis (enumeration k i)

def coordinates (k : ℕ) (Q : MvPolynomial (Fin 2) ℝ) : Fin (Fintype.card (Index k)) → ℝ :=
  fun i ↦ Q.coeff (exponent (enumeration k i))

theorem exponent_represent (k : ℕ) (m : Fin 2 →₀ ℕ) (hm : m.sum (fun _ e ↦ e) ≤ k) :
    ∃ i : Index k, exponent i = m := by
  have he : m = Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1) := by
    ext i
    fin_cases i <;> simp
  have hs : m.sum (fun _ e ↦ e) = m 0 + m 1 := by
    calc
      _ = (Finsupp.single (0 : Fin 2) (m 0) + Finsupp.single 1 (m 1)).sum (fun _ e ↦ e) :=
        congrArg (fun v : Fin 2 →₀ ℕ ↦ v.sum (fun _ e ↦ e)) he
      _ = _ := by simp [Finsupp.sum_add_index']
  let i : Index k := ⟨(⟨m 0, by omega⟩, ⟨m 1, by omega⟩), by change m 0 + m 1 ≤ k; omega⟩
  exact ⟨i, he.symm⟩

theorem reconstruction (k : ℕ) (Q : MvPolynomial (Fin 2) ℝ) (hQ : Q.totalDegree ≤ k) :
    polynomialCombination (family k) (coordinates k Q) = Q := by
  classical
  ext m
  by_cases hindex : ∃ i : Index k, exponent i = m
  · obtain ⟨i, hi⟩ := hindex
    obtain ⟨j, rfl⟩ := (enumeration k).surjective i
    subst m
    exact combination_coefficient k _ (enumeration k) (enumeration k).injective (coordinates k Q) j
  · have hz : Q.coeff m = 0 := by
      by_contra hne
      have hd := (le_totalDegree (MvPolynomial.mem_support_iff.mpr hne)).trans hQ
      exact hindex (exponent_represent k m hd)
    rw [hz]
    simp only [polynomialCombination, coeff_sum, family, basis, C_mul_monomial, mul_one, coeff_monomial]
    apply sum_eq_zero
    intro j _hj
    exact ite_eq_right (fun he ↦ (hindex ⟨enumeration k j, he⟩).elim)

theorem coordinates_ne_zero (k : ℕ) (Q : MvPolynomial (Fin 2) ℝ) (hQ : Q.totalDegree ≤ k)
    (hne : Q ≠ 0) : coordinates k Q ≠ 0 := by
  intro hc
  apply hne
  rw [← reconstruction k Q hQ, hc]
  simp [polynomialCombination]

end PaperP1.TotalDegreeMonomialFamily
