module

public import PaperP1.Analysis.LogarithmicShiftPhase
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Data.Nat.Factorial.Basic

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ReciprocalFiniteDifferences
open PaperP1

def kernel : List ℝ → ℕ → ℝ → ℝ
  | [],m,x => 1/x^m
  | h::hs,m,x => kernel hs m x-kernel hs m (x+h)

def coefficient : ℕ → List ℝ → ℝ
  | _,[] => 1
  | m,h::hs => h*(m : ℝ)*coefficient (m+1) hs

theorem rpow_negative_integer (x : ℝ) (m : ℕ) : x^(-(m : ℝ))=1/x^m := by
  rw [Real.rpow_neg_natCast,zpow_neg,zpow_natCast,one_div]

theorem base_hasDerivAt (m : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ ↦ 1/y^m) (-(m : ℝ)*(1/x^(m+1))) x := by
  have hh := Real.hasDerivAt_rpow_const (x := x) (p := -(m : ℝ)) (Or.inl hx.ne')
  convert hh using 1
  · funext y
    exact (rpow_negative_integer y m).symm
  · have he : -(m : ℝ)-1=-((m+1 : ℕ) : ℝ) := by push_cast; ring
    rw [he,rpow_negative_integer x (m+1)]

theorem hasDerivAt_kernel (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) (m : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (kernel hs m) (-(m : ℝ)*kernel hs (m+1) x) x := by
  induction hs generalizing m x with
  | nil => exact base_hasDerivAt m x hx
  | cons h hs ih =>
    have hh0 : 0 ≤ h := hhs h List.mem_cons_self
    have htail : ∀ v ∈ hs, 0 ≤ v := fun v hv ↦ hhs v (List.mem_cons_of_mem h hv)
    have hxp : 0 < x+h := by linarith only [hx,hh0]
    have hFirst := ih htail m x hx
    have hSecond : HasDerivAt (fun y : ℝ ↦ kernel hs m (y+h)) (-(m : ℝ)*kernel hs (m+1) (x+h)) x := by
      simpa only [Function.comp_def,id_eq,mul_one,one_smul] using
        (ih htail m (x+h) hxp).scomp x ((hasDerivAt_id x).add_const h)
    convert hFirst.sub hSecond using 1
    · rfl
    · dsimp only [kernel]
      ring

theorem continuousOn_kernel (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) (m : ℕ) :
    ContinuousOn (kernel hs m) (Set.Ioi 0) := by
  intro x hx
  exact (hasDerivAt_kernel hs hhs m x hx).continuousAt.continuousWithinAt

theorem coefficient_nonneg (m : ℕ) (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) : 0 ≤ coefficient m hs := by
  induction hs generalizing m with
  | nil => simp [coefficient]
  | cons h hs ih =>
    have hh0 : 0 ≤ h := hhs h List.mem_cons_self
    have htail : ∀ v ∈ hs, 0 ≤ v := fun v hv ↦ hhs v (List.mem_cons_of_mem h hv)
    exact mul_nonneg (mul_nonneg hh0 (Nat.cast_nonneg m)) (ih (m+1) htail)

theorem coefficient_identity (m : ℕ) (hs : List ℝ) :
    coefficient m hs=(m.ascFactorial hs.length : ℝ)*hs.prod := by
  induction hs generalizing m with
  | nil => simp [coefficient]
  | cons h hs ih =>
    have he : m.ascFactorial (hs.length+1)=m*(m+1).ascFactorial hs.length := by
      rw [Nat.ascFactorial_succ,← Nat.succ_ascFactorial m hs.length]
    simp only [coefficient,List.length_cons,List.prod_cons,ih,he,Nat.cast_mul]
    ring
end PaperP1.ReciprocalFiniteDifferences
