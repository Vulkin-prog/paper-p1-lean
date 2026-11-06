module

public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! # Actual standard monomial combinations cannot be multiples of the original equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.StandardMonomialFamily

open MvPolynomial Finset

variable {R σ ι : Type*} [CommRing R] [Fintype ι]

def polynomial (m : ι → σ →₀ ℕ) (w : ι → R) : MvPolynomial σ R :=
  ∑ i, monomial (m i) (w i)

theorem coeff_at (m : ι → σ →₀ ℕ) (hm : Function.Injective m) (w : ι → R) (i : ι) :
    (polynomial m w).coeff (m i) = w i := by
  classical
  simp [polynomial, hm.eq_iff]

theorem support_subset (m : ι → σ →₀ ℕ) (w : ι → R) :
    ((polynomial m w).support : Set (σ →₀ ℕ)) ⊆ Set.range m := by
  classical
  intro r hr
  by_contra hn
  have hne (i : ι) : m i ≠ r := by
    intro he
    exact hn ⟨i, he⟩
  have hz : (polynomial m w).coeff r = 0 := by
    simp only [polynomial, coeff_sum, coeff_monomial, ite_eq_right (hne _), sum_const_zero]
  exact (mem_support_iff.mp hr) hz

theorem nonzero (m : ι → σ →₀ ℕ) (hm : Function.Injective m) (w : ι → R) (hw : w ≠ 0) :
    polynomial m w ≠ 0 := by
  intro hz
  apply hw
  funext i
  have he := congrArg (fun P : MvPolynomial σ R ↦ P.coeff (m i)) hz
  simpa [coeff_at m hm] using he

theorem homogeneous (m : ι → σ →₀ ℕ) (e : ℕ) (hm : ∀ i, (m i).degree = e) (w : ι → R) :
    (polynomial m w).IsHomogeneous e := by
  apply IsHomogeneous.sum
  intro i _hi
  exact isHomogeneous_monomial (w i) (hm i)

theorem evaluation (m : ι → σ →₀ ℕ) (w : ι → R) (v : σ → R) :
    eval v (polynomial m w) = ∑ i, (m i).prod (fun j e ↦ v j ^ e) * w i := by
  classical
  rw [polynomial, map_sum]
  apply sum_congr rfl
  intro i _hi
  rw [eval_monomial, mul_comm]

theorem map_coefficients {S : Type*} [CommRing S] (φ : R →+* S)
    (m : ι → σ →₀ ℕ) (w : ι → R) :
    map φ (polynomial m w) = polynomial m (fun i ↦ φ (w i)) := by
  simp only [polynomial, map_sum, map_monomial]

variable [IsDomain R]

theorem not_dvd (o : MonomialOrder σ) (q : MvPolynomial σ R) (hq : q ≠ 0)
    (m : ι → σ →₀ ℕ) (hm : Function.Injective m) (hstandard : ∀ i, ¬ o.degree q ≤ m i)
    (w : ι → R) (hw : w ≠ 0) : ¬ q ∣ polynomial m w := by
  classical
  have hnonzero := nonzero m hm w hw
  have hs := support_subset m w (o.degree_mem_support hnonzero)
  obtain ⟨i, he⟩ := hs
  rintro ⟨A, hA⟩
  have hA0 : A ≠ 0 := by
    intro hz
    exact hnonzero (by rw [hA, hz, mul_zero])
  have hdegree : o.degree q ≤ o.degree (polynomial m w) := by
    rw [hA, o.degree_mul hq hA0]
    exact le_self_add
  exact hstandard i (he.symm ▸ hdegree)

end PaperP1.StandardMonomialFamily
