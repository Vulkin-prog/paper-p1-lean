module

public import PaperP1.Analysis.PolyaChebyshevCriterion
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Linear independence on every nonempty parameter subinterval

Normalization followed by differentiation preserves this local property.
The proof uses the actual derivative-zero constant theorem on each interval.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalLinearIndependence

open Set Finset RecursiveChebyshev

def Independent {n : ℕ} (f : Fin n → ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ a b : ℝ, a < b → Ioo a b ⊆ s → ∀ c : Fin n → ℝ, c ≠ 0 →
    ∃ x ∈ Ioo a b, combination f c x ≠ 0

theorem mono {n : ℕ} (f : Fin n → ℝ → ℝ) (s t : Set ℝ)
    (hf : Independent f s) (ht : t ⊆ s) : Independent f t := by
  intro a b hab hsub c hc
  exact hf a b hab (hsub.trans ht) c hc

theorem first_nonzero (n : ℕ) (a b : ℝ) (hab : a < b) (f : Fin (n + 1) → ℝ → ℝ)
    (hf : Independent f (Ioo a b)) : ∃ x ∈ Ioo a b, f 0 x ≠ 0 := by
  let c : Fin (n + 1) → ℝ := Fin.cons 1 (fun _ ↦ 0)
  have hc : c ≠ 0 := by
    intro he
    have hh := congrFun he 0
    simp only [c, Fin.cons_zero, Pi.zero_apply, one_ne_zero] at hh
  obtain ⟨x, hx, hnon⟩ := hf a b hab Subset.rfl c hc
  refine ⟨x, hx, ?_⟩
  simpa [combination, c, Fin.sum_univ_succ] using hnon

theorem normalized_independent (n : ℕ) (a b : ℝ) (f : Fin (n + 1) → ℝ → ℝ)
    (hdiff : ∀ i, DifferentiableOn ℝ (f i) (Ioo a b))
    (hnon : ∀ x ∈ Ioo a b, f 0 x ≠ 0) (hf : Independent f (Ioo a b)) :
    Independent (normalizedDerivative f) (Ioo a b) := by
  classical
  intro u v huv hsub d hd
  by_contra hbad
  push Not at hbad
  let c : Fin (n + 1) → ℝ := Fin.cons 0 d
  let H : ℝ → ℝ := fun x ↦ combination f c x / f 0 x
  have hcombo : DifferentiableOn ℝ (combination f c) (Ioo a b) := by
    change DifferentiableOn ℝ (fun x ↦ ∑ i, c i * f i x) (Ioo a b)
    exact DifferentiableOn.fun_sum (u := Finset.univ) (fun i _hi ↦ (hdiff i).const_mul (c i))
  have hH : DifferentiableOn ℝ H (Ioo u v) := (hcombo.div (hdiff 0) hnon).mono hsub
  have hder : EqOn (deriv H) 0 (Ioo u v) := by
    intro x hx
    have he := normalized_derivative a b f hdiff hnon c (hsub hx)
    exact he.trans (hbad x hx)
  obtain ⟨K, hK⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo hH hder
  let w : Fin (n + 1) → ℝ := Fin.cons (-K) d
  have hw : w ≠ 0 := by
    intro he
    apply hd
    funext i
    exact congrFun he i.succ
  obtain ⟨x, hx, hxnon⟩ := hf u v huv hsub w hw
  have he : combination f w x / f 0 x = -K + H x := by
    rw [normalized_identity f w x (hnon x (hsub hx))]
    dsimp only [H]
    rw [normalized_identity f c x (hnon x (hsub hx))]
    simp only [w, c, Fin.cons_zero, Fin.cons_succ, zero_add]
  have hzero : combination f w x / f 0 x = 0 := by rw [he, hK x hx]; ring
  exact hxnon (by simpa only [zero_mul] using (div_eq_iff (hnon x (hsub hx))).mp hzero)

end PaperP1.LocalLinearIndependence
