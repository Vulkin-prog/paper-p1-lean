module

public import PaperP1.Analysis.FiniteRolleZeros
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # A finite Chebyshev criterion from nonvanishing normalized pivots

Repeated division by the first function and differentiation reduces the family.
The criterion proves an actual zero bound, without assuming one as an input.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RecursiveChebyshev

open Finset Set

def combination {n : ℕ} (f : Fin n → ℝ → ℝ) (c : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i, c i * f i x

def normalizedDerivative {n : ℕ} (f : Fin (n + 1) → ℝ → ℝ) : Fin n → ℝ → ℝ :=
  fun i ↦ deriv (fun x ↦ f i.succ x / f 0 x)

def Admissible : (n : ℕ) → (Fin n → ℝ → ℝ) → ℝ → ℝ → Prop
  | 0, _, _, _ => True
  | n + 1, f, a, b =>
      (∀ i, DifferentiableOn ℝ (f i) (Ioo a b)) ∧
      (∀ x ∈ Ioo a b, f 0 x ≠ 0) ∧ Admissible n (normalizedDerivative f) a b

theorem normalized_identity {n : ℕ} (f : Fin (n + 1) → ℝ → ℝ)
    (c : Fin (n + 1) → ℝ) (x : ℝ) (hzero : f 0 x ≠ 0) :
    combination f c x / f 0 x = c 0 + ∑ i : Fin n, c i.succ * (f i.succ x / f 0 x) := by
  rw [combination, Fin.sum_univ_succ, add_div]
  simp only [mul_div_cancel_right₀ _ hzero, sum_div, mul_div_assoc]

theorem normalized_derivative {n : ℕ} (a b : ℝ) (f : Fin (n + 1) → ℝ → ℝ)
    (hf : ∀ i, DifferentiableOn ℝ (f i) (Ioo a b))
    (hnon : ∀ x ∈ Ioo a b, f 0 x ≠ 0) (c : Fin (n + 1) → ℝ) :
    EqOn (deriv (fun x ↦ combination f c x / f 0 x))
      (combination (normalizedDerivative f) (fun i ↦ c i.succ)) (Ioo a b) := by
  have heq : EqOn (fun x ↦ combination f c x / f 0 x)
      (fun x ↦ c 0 + ∑ i : Fin n, c i.succ * (f i.succ x / f 0 x)) (Ioo a b) :=
    fun x hx ↦ normalized_identity f c x (hnon x hx)
  intro x hx
  rw [heq.deriv isOpen_Ioo hx, deriv_const_add]
  have hd (i : Fin n) : DifferentiableAt ℝ (fun y ↦ c i.succ * (f i.succ y / f 0 y)) x :=
    (((hf i.succ).differentiableAt (isOpen_Ioo.mem_nhds hx)).div
      ((hf 0).differentiableAt (isOpen_Ioo.mem_nhds hx)) (hnon x hx)).const_mul _
  rw [deriv_fun_sum (fun i _hi ↦ hd i)]
  simp only [combination, normalizedDerivative, deriv_const_mul_field]

theorem card_lt {n : ℕ} (a b : ℝ) (f : Fin n → ℝ → ℝ)
    (hf : Admissible n f a b) (c : Fin n → ℝ) (hc : c ≠ 0)
    (S : Finset ℝ) (hS : ∀ x ∈ S, x ∈ Ioo a b ∧ combination f c x = 0) : S.card < n := by
  classical
  induction n generalizing S with
  | zero => exact False.elim (hc (funext (fun i ↦ Fin.elim0 i)))
  | succ n ih =>
    obtain ⟨hdiff, hnon, hrec⟩ := hf
    by_cases htail : ∀ i : Fin n, c i.succ = 0
    · have hc₀ : c 0 ≠ 0 := by
        intro hz
        apply hc
        funext i
        exact Fin.cases hz (fun j ↦ htail j) i
      have hempty : S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hzero := (hS x hx).2
        simp only [combination, Fin.sum_univ_succ, htail, zero_mul, sum_const_zero, add_zero] at hzero
        exact mul_ne_zero hc₀ (hnon x (hS x hx).1) hzero
      simp [hempty]
    · have htailNe : (fun i : Fin n ↦ c i.succ) ≠ 0 := by
        intro hz
        apply htail
        intro i
        exact congrFun hz i
      let u : ℝ → ℝ := fun x ↦ combination f c x / f 0 x
      have hcombo : DifferentiableOn ℝ (combination f c) (Ioo a b) := by
        change DifferentiableOn ℝ (fun x ↦ ∑ i, c i * f i x) (Ioo a b)
        exact DifferentiableOn.fun_sum (u := univ) (fun i _hi ↦ (hdiff i).const_mul (c i))
      have hu : ContinuousOn u (Ioo a b) := (hcombo.div (hdiff 0) hnon).continuousOn
      have hSu : ∀ x ∈ S, x ∈ Ioo a b ∧ u x = 0 := by
        intro x hx
        exact ⟨(hS x hx).1, by dsimp only [u]; rw [(hS x hx).2, zero_div]⟩
      obtain ⟨T, hT, hcard⟩ := FiniteRolleZeros.exists_derivative_zeros a b u hu S hSu
      have hTzero : ∀ x ∈ T, x ∈ Ioo a b ∧
          combination (normalizedDerivative f) (fun i ↦ c i.succ) x = 0 := by
        intro x hx
        refine ⟨(hT x hx).1, ?_⟩
        rw [← normalized_derivative a b f hdiff hnon c (hT x hx).1]
        exact (hT x hx).2
      have hb := ih (normalizedDerivative f) hrec (fun i ↦ c i.succ) htailNe T hTzero
      omega

theorem coefficients_eq_zero {n : ℕ} (a b : ℝ) (f : Fin n → ℝ → ℝ)
    (hf : Admissible n f a b) (S : Finset ℝ) (hcard : n ≤ S.card)
    (c : Fin n → ℝ) (hS : ∀ x ∈ S, x ∈ Ioo a b ∧ combination f c x = 0) : c = 0 := by
  by_contra hc
  have hh := card_lt a b f hf c hc S hS
  omega

theorem evaluation_injective {n : ℕ} (a b : ℝ) (f : Fin n → ℝ → ℝ)
    (hf : Admissible n f a b) (S : Finset ℝ) (hcard : n ≤ S.card)
    (hS : ∀ x ∈ S, x ∈ Ioo a b) :
    Function.Injective (fun c : Fin n → ℝ ↦ fun x : S ↦ combination f c x) := by
  intro c d heq
  apply sub_eq_zero.mp
  apply coefficients_eq_zero a b f hf S hcard (c - d)
  intro x hx
  refine ⟨hS x hx, ?_⟩
  have hh := congrFun heq ⟨x, hx⟩
  change combination f c x = combination f d x at hh
  simpa only [combination, Pi.sub_apply, sub_mul, sum_sub_distrib] using sub_eq_zero.mpr hh

end PaperP1.RecursiveChebyshev
