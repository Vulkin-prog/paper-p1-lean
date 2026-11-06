module

public import PaperP1.Algebra.FiniteGradedModuleSandwich
public import PaperP1.Algebra.GradedHilbertPolynomial
public import PaperP1.Algebra.PolynomialEventualCoefficientOrder

/-! # A finite graded domain extension multiplies the actual top Hilbert coefficient by its rank -/

set_option autoImplicit false

@[expose] public noncomputable section

open scoped Classical

namespace PaperP1.FiniteGradedHilbertCoefficient

open Polynomial Finset

theorem translations_degree {ι : Type*} [Fintype ι] (p : ℚ[X]) (r : ℕ)
    (hp : p.natDegree ≤ r) (t : ι → ℚ) :
    (∑ i, p.comp (X + C (t i))).natDegree ≤ r := by
  exact natDegree_sum_le_of_forall_le _ _ (fun i _hi ↦
    PolynomialEventualCoefficientOrder.translation_degree_le p (t i) r hp)

theorem translations_coefficient {ι : Type*} [Fintype ι] (p : ℚ[X]) (r : ℕ)
    (hp : p.natDegree ≤ r) (t : ι → ℚ) :
    (∑ i, p.comp (X + C (t i))).coeff r = (Fintype.card ι : ℚ) * p.coeff r := by
  simp only [finsetSum_coeff, PolynomialEventualCoefficientOrder.translation_coefficient p _ r hp,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

variable {F A B ι : Type*} [Field F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B] [Fintype ι]
  {G : ℕ → Submodule F A} {H : ℕ → Submodule F B}

theorem shifted_sum (p : ℚ[X]) {M : ℕ}
    (hp : ∀ n : ℕ, M ≤ n → (Module.finrank F (G n) : ℚ) = p.eval (n : ℚ))
    (w : ι → ℕ) (t n : ℕ) (hn : ∀ i, M + w i ≤ n + t) :
    (∑ i, (Module.finrank F (G (n + t - w i)) : ℚ)) =
      (∑ i, p.comp (X + C ((t : ℚ) - (w i : ℚ)))).eval (n : ℚ) := by
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [hp _ (by have := hn i; omega), eval_comp, eval_add, eval_X, eval_C]
  congr 1
  rw [Nat.cast_sub (by have := hn i; omega), Nat.cast_add]
  ring

variable [GradedAlgebra G] [GradedAlgebra H]
  (f : G →+*ᵍ H) (hscalar : ∀ a : F, f (algebraMap F A a) = algebraMap F B a)
  (v : ι → B) (w : ι → ℕ) (hv : ∀ i, v i ∈ H (w i))

include hscalar hv in
theorem coefficient_eq [IsDomain A] [IsDomain B] (hinj : Function.Injective f)
    (hgen : letI : Algebra A B := f.toRingHom.toAlgebra
      Submodule.span A (Set.range v) = ⊤)
    (hfin : ∀ n : ℕ, Module.Finite F (G n)) (p q : ℚ[X]) (r : ℕ)
    (hpdeg : p.natDegree ≤ r) (hqdeg : q.natDegree ≤ r)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial G p)
    (hq : GradedHilbertPolynomial.IsHilbertPolynomial H q) :
    letI : Algebra A B := f.toRingHom.toAlgebra
    q.coeff r = (Module.finrank A B : ℚ) * p.coeff r := by
  let : Algebra A B := f.toRingHom.toAlgebra
  obtain ⟨s, m, N, hcard, hsandwich⟩ :=
    FiniteGradedModuleSandwich.exists_sandwich f hscalar v w hv hinj hgen hfin
  obtain ⟨M, hM⟩ := hp
  obtain ⟨L, hL⟩ := hq
  let T := max N (max M L + univ.sup w)
  have htail : ∀ n : ℕ, T ≤ n →
      (∑ i : s, p.comp (X + C (-(w i : ℚ)))).eval (n : ℚ) ≤ q.eval (n : ℚ) ∧
      q.eval (n : ℚ) ≤ (∑ i : s, p.comp (X + C ((m : ℚ) - (w i : ℚ)))).eval (n : ℚ) := by
    intro n hn
    have hnN : N ≤ n := (le_max_left _ _).trans hn
    have hrest : max M L + univ.sup w ≤ n := (le_max_right _ _).trans hn
    have hnL : L ≤ n := (le_max_right M L).trans ((Nat.le_add_right _ _).trans hrest)
    have hw (i : s) : M + w i ≤ n := by
      exact (Nat.add_le_add (le_max_left M L)
        (Finset.le_sup (f := w) (Finset.mem_univ (i : ι)))).trans hrest
    obtain ⟨_, hlo, hup⟩ := hsandwich n hnN
    have hloQ : (∑ i : s, (Module.finrank F (G (n - w i)) : ℚ)) ≤
        (Module.finrank F (H n) : ℚ) := by exact_mod_cast hlo
    have hupQ : (Module.finrank F (H n) : ℚ) ≤
        ∑ i : s, (Module.finrank F (G (n + m - w i)) : ℚ) := by exact_mod_cast hup
    have he0 := shifted_sum p (fun n hn ↦ (hM n hn).symm) (fun i : s ↦ w i) 0 n
      (fun i ↦ by simpa only [Nat.add_zero] using hw i)
    have hem := shifted_sum p (fun n hn ↦ (hM n hn).symm) (fun i : s ↦ w i) m n
      (fun i ↦ (hw i).trans (Nat.le_add_right n m))
    simp only [Nat.add_zero, Nat.cast_zero, zero_sub] at he0
    rw [he0, ← hL n hnL] at hloQ
    rw [hem, ← hL n hnL] at hupQ
    exact ⟨hloQ, hupQ⟩
  have hlo := PolynomialEventualCoefficientOrder.coefficient_le _ q r
    (translations_degree p r hpdeg _) hqdeg T (fun n hn ↦ (htail n hn).1)
  have hup := PolynomialEventualCoefficientOrder.coefficient_le q _ r hqdeg
    (translations_degree p r hpdeg _) T (fun n hn ↦ (htail n hn).2)
  rw [translations_coefficient p r hpdeg, Fintype.card_coe, hcard] at hlo hup
  exact le_antisymm hup hlo

end PaperP1.FiniteGradedHilbertCoefficient
