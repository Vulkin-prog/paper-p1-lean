module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-! # Rational interpolation on more than twice the degree many abscissae -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalInterpolationUniqueness

open Polynomial

variable {F : Type*} [Field F]

def Interpolates (S : Finset F) (y : F → F) (P Q : F[X]) : Prop :=
  ∀ t ∈ S, P.eval t = y t * Q.eval t

theorem cross_product (a : ℕ) (S : Finset F) (y : F → F) (P Q P' Q' : F[X])
    (hP : P.natDegree ≤ a) (hQ : Q.natDegree ≤ a)
    (hP' : P'.natDegree ≤ a) (hQ' : Q'.natDegree ≤ a) (hcard : 2 * a < S.card)
    (hfirst : Interpolates S y P Q) (hsecond : Interpolates S y P' Q') :
    P * Q' = P' * Q := by
  apply sub_eq_zero.mp
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ S
  · intro t ht
    rw [eval_sub, eval_mul, eval_mul, hfirst t ht, hsecond t ht]
    ring
  · have hd : (P * Q' - P' * Q).natDegree ≤ 2 * a :=
      (natDegree_sub_le _ _).trans (max_le
        ((natDegree_mul_le.trans (Nat.add_le_add hP hQ')).trans (by omega))
        ((natDegree_mul_le.trans (Nat.add_le_add hP' hQ)).trans (by omega)))
    exact hd.trans_lt hcard

theorem common_factor (P Q P' Q' : F[X]) (hQ : Q ≠ 0) (hcop : IsCoprime P Q)
    (hcross : P * Q' = P' * Q) : ∃ H : F[X], P' = H * P ∧ Q' = H * Q := by
  have hdiv : Q ∣ Q' := hcop.symm.dvd_of_dvd_mul_left ⟨P', by rw [hcross, mul_comm]⟩
  obtain ⟨H, hH⟩ := hdiv
  refine ⟨H, ?_, hH.trans (mul_comm _ _)⟩
  apply mul_right_cancel₀ hQ
  calc
    P' * Q = P * Q' := hcross.symm
    _ = (H * P) * Q := by rw [hH]; ring

theorem common_factor_constant (a : ℕ) (P Q P' Q' : F[X]) (hQ : Q ≠ 0)
    (hcop : IsCoprime P Q) (hdegree : max P.natDegree Q.natDegree = a)
    (hP' : P'.natDegree ≤ a) (hQ' : Q'.natDegree ≤ a) (hcross : P * Q' = P' * Q) :
    ∃ δ : F, P' = C δ * P ∧ Q' = C δ * Q := by
  obtain ⟨H, hHP, hHQ⟩ := common_factor P Q P' Q' hQ hcop hcross
  have hdegH : H.natDegree = 0 := by
    by_cases hH : H = 0
    · simp only [hH, natDegree_zero]
    by_cases hP : P = 0
    · have hqa : Q.natDegree = a := by simpa only [hP, natDegree_zero, zero_max] using hdegree
      have h := hQ'
      rw [hHQ, natDegree_mul hH hQ, hqa] at h
      omega
    · have hp := hP'
      have hq := hQ'
      rw [hHP, natDegree_mul hH hP] at hp
      rw [hHQ, natDegree_mul hH hQ] at hq
      omega
  exact ⟨H.coeff 0, (eq_C_of_natDegree_eq_zero hdegH) ▸ hHP,
    (eq_C_of_natDegree_eq_zero hdegH) ▸ hHQ⟩

theorem unique_up_to_scalar (a : ℕ) (S : Finset F) (y : F → F) (P Q P' Q' : F[X])
    (hQ0 : Q ≠ 0) (hcop : IsCoprime P Q) (hdegree : max P.natDegree Q.natDegree = a)
    (hP' : P'.natDegree ≤ a) (hQ' : Q'.natDegree ≤ a) (hcard : 2 * a < S.card)
    (hfirst : Interpolates S y P Q) (hsecond : Interpolates S y P' Q') :
    ∃ δ : F, P' = C δ * P ∧ Q' = C δ * Q :=
  common_factor_constant a P Q P' Q' hQ0 hcop hdegree hP' hQ'
    (cross_product a S y P Q P' Q' ((le_max_left _ _).trans_eq hdegree)
      ((le_max_right _ _).trans_eq hdegree) hP' hQ' hcard hfirst hsecond)

theorem cross_product_family {ι : Type*} [Fintype ι] (a : ℕ) (x y : ι → F)
    (hinj : Function.Injective x) (P Q P' Q' : F[X])
    (hP : P.natDegree ≤ a) (hQ : Q.natDegree ≤ a)
    (hP' : P'.natDegree ≤ a) (hQ' : Q'.natDegree ≤ a) (hcard : 2 * a < Fintype.card ι)
    (hfirst : ∀ j, P.eval (x j) = y j * Q.eval (x j))
    (hsecond : ∀ j, P'.eval (x j) = y j * Q'.eval (x j)) : P * Q' = P' * Q := by
  apply sub_eq_zero.mp
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hinj
  · intro j
    rw [eval_sub, eval_mul, eval_mul, hfirst j, hsecond j]
    ring
  · have hd : (P * Q' - P' * Q).natDegree ≤ 2 * a :=
      (natDegree_sub_le _ _).trans (max_le
        ((natDegree_mul_le.trans (Nat.add_le_add hP hQ')).trans (by omega))
        ((natDegree_mul_le.trans (Nat.add_le_add hP' hQ)).trans (by omega)))
    exact hd.trans_lt hcard

theorem unique_up_to_scalar_family {ι : Type*} [Fintype ι] (a : ℕ) (x y : ι → F)
    (hinj : Function.Injective x) (P Q P' Q' : F[X]) (hQ0 : Q ≠ 0) (hcop : IsCoprime P Q)
    (hdegree : max P.natDegree Q.natDegree = a) (hP' : P'.natDegree ≤ a) (hQ' : Q'.natDegree ≤ a)
    (hcard : 2 * a < Fintype.card ι) (hfirst : ∀ j, P.eval (x j) = y j * Q.eval (x j))
    (hsecond : ∀ j, P'.eval (x j) = y j * Q'.eval (x j)) :
    ∃ δ : F, P' = C δ * P ∧ Q' = C δ * Q :=
  common_factor_constant a P Q P' Q' hQ0 hcop hdegree hP' hQ'
    (cross_product_family a x y hinj P Q P' Q' ((le_max_left _ _).trans_eq hdegree)
      ((le_max_right _ _).trans_eq hdegree) hP' hQ' hcard hfirst hsecond)

end PaperP1.RationalInterpolationUniqueness
