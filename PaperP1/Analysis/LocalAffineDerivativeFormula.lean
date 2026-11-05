module

public import PaperP1.Analysis.IteratedDerivativeMonotonicity
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic.Ring

/-! # Actual affine reparametrization derivatives on local smooth domains

Only local C-infinity regularity on the actual interval is required. No global
smooth extension of the function is introduced.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalAffineDerivativeFormula

open Set IteratedDerivativeMonotonicity
open scoped ContDiff

def parameter (u c t : ℝ) : ℝ := u + c * t

theorem hasDerivAt_parameter (u c t : ℝ) : HasDerivAt (parameter u c) c t := by
  change HasDerivAt (fun v : ℝ ↦ u + c * v) c t
  exact (hasDerivAt_const_mul c).const_add u

theorem contDiff_parameter (u c : ℝ) (n : WithTop ℕ∞) : ContDiff ℝ n (parameter u c) := by
  change ContDiff ℝ n (fun t : ℝ ↦ u + c * t)
  exact contDiff_const.add (contDiff_const.mul contDiff_id)

theorem iterated_formula (f : ℝ → ℝ) (a b : ℝ) (hf : ContDiffOn ℝ ∞ f (Ioo a b))
    (u c : ℝ) (n : ℕ) :
    EqOn (iteratedDeriv n (fun t ↦ f (parameter u c t)))
      (fun t ↦ c ^ n * iteratedDeriv n f (parameter u c t))
      ((parameter u c) ⁻¹' Ioo a b) := by
  have hopen : IsOpen ((parameter u c) ⁻¹' Ioo a b) :=
    isOpen_Ioo.preimage (contDiff_parameter u c 1).continuous
  induction n with
  | zero =>
    intro t _ht
    simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ n ih =>
    intro t ht
    have hn := smooth_iterated f a b hf n
    have hN : HasDerivAt (iteratedDeriv n f)
        (iteratedDeriv (n + 1) f (parameter u c t)) (parameter u c t) := by
      rw [iteratedDeriv_succ]
      exact ((hn.differentiableOn (by simp) (parameter u c t) ht).differentiableAt
        (isOpen_Ioo.mem_nhds ht)).hasDerivAt
    have hG : HasDerivAt (fun v ↦ c ^ n * iteratedDeriv n f (parameter u c v))
        (c ^ (n + 1) * iteratedDeriv (n + 1) f (parameter u c t)) t :=
      ((hN.comp t (hasDerivAt_parameter u c t)).const_mul (c ^ n)).congr_deriv
        (by rw [pow_succ]; ring)
    rw [iteratedDeriv_succ]
    exact ((ih.deriv hopen) ht).trans hG.deriv

theorem smooth_composition (f : ℝ → ℝ) (a b : ℝ) (hf : ContDiffOn ℝ ∞ f (Ioo a b))
    (u c : ℝ) (s : Set ℝ) (hmap : MapsTo (parameter u c) s (Ioo a b)) :
    ContDiffOn ℝ ∞ (fun t ↦ f (parameter u c t)) s :=
  hf.comp (contDiff_parameter u c ∞).contDiffOn hmap

theorem positive_parameter_derivative (u c : ℝ) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    iteratedDeriv n (parameter u c) t = if n = 1 then c else 0 := by
  change iteratedDeriv n (fun t : ℝ ↦ u + c * t) t = _
  rw [iteratedDeriv_const_add (by omega) u, iteratedDeriv_const_mul_field]
  have hi : iteratedDeriv n (fun x : ℝ ↦ x) t = if n = 0 then t else if n = 1 then 1 else 0 :=
    iteratedDeriv_fun_id
  rw [hi, ite_eq_right (by omega)]
  split_ifs <;> simp

theorem image_parameter (u c : ℝ) (hc : 0 < c) (x : ℝ) (hx : x ∈ Ioo u (u + c)) :
    ∃ t ∈ Ioo (0 : ℝ) 1, parameter u c t = x := by
  refine ⟨(x - u) / c, ?_, ?_⟩
  · constructor
    · exact div_pos (sub_pos.mpr hx.1) hc
    · exact (div_lt_one hc).mpr (by linarith [hx.2])
  · dsimp only [parameter]
    field_simp [hc.ne']
    ring

end PaperP1.LocalAffineDerivativeFormula
