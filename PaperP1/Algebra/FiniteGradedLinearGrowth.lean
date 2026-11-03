module

public import PaperP1.Algebra.FiniteGradedModuleSandwich
public import PaperP1.Algebra.LinearHilbertGrowth
public import Lean.Elab.Tactic.Omega

/-! # Actual finite graded domain extensions multiply the linear Hilbert slope by their rank -/

set_option autoImplicit false

@[expose] public noncomputable section

open scoped Classical

namespace PaperP1.FiniteGradedLinearGrowth

open Polynomial Finset LinearHilbertGrowth

variable {F A B ι : Type*} [Field F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B] [Fintype ι]
  {G : ℕ → Submodule F A} {H : ℕ → Submodule F B}

theorem shifted_sum (a b : ℚ) {M : ℕ}
    (hbase : ∀ n : ℕ, M ≤ n → function G n = a * (n : ℚ) + b)
    (w : ι → ℕ) (t n : ℕ) (hn : ∀ i, M + w i ≤ n + t) :
    (∑ i, (Module.finrank F (G (n + t - w i)) : ℚ)) =
      (Fintype.card ι : ℚ) * a * (n : ℚ) + ∑ i, (b + a * ((t : ℚ) - (w i : ℚ))) := by
  have he (i : ι) : (Module.finrank F (G (n + t - w i)) : ℚ) =
      a * (n : ℚ) + (b + a * ((t : ℚ) - (w i : ℚ))) := by
    change function G (n + t - w i) = _
    rw [hbase _ (by have := hn i; omega), Nat.cast_sub (by have := hn i; omega), Nat.cast_add]
    ring
  simp_rw [he, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

variable [GradedAlgebra G] [GradedAlgebra H]
  (f : G →+*ᵍ H) (hscalar : ∀ a : F, f (algebraMap F A a) = algebraMap F B a)
  (v : ι → B) (w : ι → ℕ) (hv : ∀ i, v i ∈ H (w i))

include hscalar hv in
theorem hasSlope [IsDomain A] [IsDomain B] (hinj : Function.Injective f)
    (hgen : letI : Algebra A B := f.toRingHom.toAlgebra
      Submodule.span A (Set.range v) = ⊤)
    (hfin : ∀ n : ℕ, Module.Finite F (G n)) (a b : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial G (C a * X + C b)) :
    letI : Algebra A B := f.toRingHom.toAlgebra
    HasSlope (function H) ((Module.finrank A B : ℚ) * a) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  obtain ⟨s, m, N, hcard, hsandwich⟩ :=
    FiniteGradedModuleSandwich.exists_sandwich f hscalar v w hv hinj hgen hfin
  obtain ⟨M, hM⟩ := hp
  have hbase (n : ℕ) (hn : M ≤ n) : function G n = a * (n : ℚ) + b := by
    have he := hM n hn
    simpa only [eval_add, eval_mul, eval_C, eval_X, function] using he.symm
  let c₀ : ℚ := ∑ i : s, (b + a * ((0 : ℚ) - (w i : ℚ)))
  let cₘ : ℚ := ∑ i : s, (b + a * ((m : ℚ) - (w i : ℚ)))
  refine ⟨|c₀| + |cₘ|, max N (M + univ.sup w), fun n hn ↦ ?_⟩
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnM : M + univ.sup w ≤ n := (le_max_right _ _).trans hn
  have hnweight (i : s) : M + w i ≤ n :=
    (Nat.add_le_add_left (Finset.le_sup (f := w) (Finset.mem_univ (i : ι))) M).trans hnM
  obtain ⟨_, hlow, hupp⟩ := hsandwich n hnN
  have hl : (∑ i : s, (Module.finrank F (G (n - w i)) : ℚ)) ≤ function H n := by
    unfold function
    exact_mod_cast hlow
  have hu : function H n ≤ ∑ i : s, (Module.finrank F (G (n + m - w i)) : ℚ) := by
    unfold function
    exact_mod_cast hupp
  have he0 := shifted_sum a b hbase (fun i : s ↦ w i) 0 n (fun i ↦ by simpa using hnweight i)
  have hem := shifted_sum a b hbase (fun i : s ↦ w i) m n
    (fun i ↦ (hnweight i).trans (Nat.le_add_right n m))
  simp only [Nat.add_zero, Fintype.card_coe, hcard] at he0 hem
  rw [he0] at hl
  rw [hem] at hu
  change (Module.finrank A B : ℚ) * a * (n : ℚ) + c₀ ≤ function H n at hl
  change function H n ≤ (Module.finrank A B : ℚ) * a * (n : ℚ) + cₘ at hu
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le c₀, abs_nonneg cₘ]
  · linarith [le_abs_self cₘ, abs_nonneg c₀]

include hscalar hv in
theorem coefficient_eq [IsDomain A] [IsDomain B] (hinj : Function.Injective f)
    (hgen : letI : Algebra A B := f.toRingHom.toAlgebra
      Submodule.span A (Set.range v) = ⊤)
    (hfin : ∀ n : ℕ, Module.Finite F (G n)) (a b : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial G (C a * X + C b))
    (p : ℚ[X]) (hP : GradedHilbertPolynomial.IsHilbertPolynomial H p) :
    letI : Algebra A B := f.toRingHom.toAlgebra
    p.coeff 1 = (Module.finrank A B : ℚ) * a :=
  LinearHilbertGrowth.coefficient_eq (hasSlope f hscalar v w hv hinj hgen hfin a b hp) hP

include hscalar hv in
theorem multiplicity [IsDomain A] [IsDomain B] (hinj : Function.Injective f)
    (hgen : letI : Algebra A B := f.toRingHom.toAlgebra
      Submodule.span A (Set.range v) = ⊤)
    (hfin : ∀ n : ℕ, Module.Finite F (G n)) (a b : ℚ) (ha : 0 < a)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial G (C a * X + C b))
    (hP : ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial H p) :
    letI : Algebra A B := f.toRingHom.toAlgebra
    GradedHilbertPolynomial.multiplicity H hP = (Module.finrank A B : ℚ) * a := by
  let : Algebra A B := f.toRingHom.toAlgebra
  have : Module.Finite A B := FreeApproximationRank.finite_of_span v hgen
  have hr : 0 < Module.finrank A B := by
    have hh := LinearMap.finrank_le_finrank_of_injective
      (f := Algebra.linearMap A B) hinj
    exact lt_of_lt_of_le (by decide : 0 < 1) (by simpa only [Module.finrank_self] using hh)
  have hslope := hasSlope f hscalar v w hv hinj hgen hfin a b hp
  have hcoeff := LinearHilbertGrowth.coefficient_eq hslope hP.choose_spec
  have hdeg : hP.choose.natDegree = 1 := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
      (LinearHilbertGrowth.polynomial_natDegree_le_one hslope hP.choose_spec)
    rw [hcoeff]
    exact ne_of_gt (mul_pos (Nat.cast_pos.mpr hr) ha)
  rw [GradedHilbertPolynomial.multiplicity_eq _ _ _ hP.choose_spec, Polynomial.leadingCoeff, hdeg,
    hcoeff]
  simp

end PaperP1.FiniteGradedLinearGrowth
