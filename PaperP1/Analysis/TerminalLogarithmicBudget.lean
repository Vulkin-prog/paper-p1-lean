module

public import PaperP1.Analysis.SpacedShiftDifferencing
public import PaperP1.Analysis.IteratedLogarithmicPhase
public import PaperP1.Analysis.IteratedLogarithmicSum
public import PaperP1.Analysis.ReciprocalDifferenceBounds
public import PaperP1.Analysis.RecursiveLogarithmicDifferencing

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.TerminalLogarithmicBudget
open Finset PaperP1
open scoped Classical

def budget (X A K n : ℕ) (t : ℝ) : ℝ :=
  2*(3 : ℝ)^(n+1)*(X : ℝ)^n/(|t| * (n.factorial : ℝ)*(A : ℝ)^n)+
  |t| * (n.factorial : ℝ)*((A*K : ℕ) : ℝ)^n/(X : ℝ)^(n+1)

theorem sum_upper (hs : List ℝ) (U : ℝ) (hhs : ∀ h ∈ hs, h ≤ U) : hs.sum ≤ (hs.length : ℝ)*U := by
  induction hs with
  | nil => simp
  | cons h hs ih =>
    have hh := hhs h List.mem_cons_self
    have hTail : ∀ v ∈ hs, v ≤ U := fun v hv ↦ hhs v (List.mem_cons_of_mem h hv)
    have hRest := ih hTail
    simp only [List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith only [hh,hRest]

theorem product_bounds (hs : List ℝ) (A U : ℝ) (hA : 0 ≤ A) (hU : 0 ≤ U)
    (hhs : ∀ h ∈ hs, A ≤ h ∧ h ≤ U) : A^hs.length ≤ hs.prod ∧ hs.prod ≤ U^hs.length := by
  induction hs with
  | nil => simp
  | cons h hs ih =>
    have hh := hhs h List.mem_cons_self
    have hTail : ∀ v ∈ hs, A ≤ v ∧ v ≤ U := fun v hv ↦ hhs v (List.mem_cons_of_mem h hv)
    obtain ⟨hL,hR⟩ := ih hTail
    have hProd : 0 ≤ hs.prod := (pow_nonneg hA _).trans hL
    have hLow := mul_le_mul hh.1 hL (pow_nonneg hA _) (hA.trans hh.1)
    have hHigh := mul_le_mul hh.2 hR hProd hU
    constructor
    · simpa only [List.length_cons,List.prod_cons,pow_succ,mul_comm] using hLow
    · simpa only [List.length_cons,List.prod_cons,pow_succ,mul_comm] using hHigh

theorem budget_nonneg (X A K n : ℕ) (t : ℝ) : 0 ≤ budget X A K n t := by unfold budget; positivity

theorem leaf_bound (X A K n : ℕ) (hX : 0 < X) (hA : 0 < A) (hK : 0 < K) (hSpan : n*(A*K) ≤ X)
    (t : ℝ) (ht : t ≠ 0) (hs : List ℝ) (hLen : hs.length=n)
    (hhs : ∀ h ∈ hs, (A : ℝ) ≤ h ∧ h ≤ ((A*K : ℕ) : ℝ)) (L : ℕ) (hLX : L ≤ X) :
    ‖∑ j ∈ Ico X (X+L), IteratedLogarithmicPhase.function hs t j‖ ≤ (X : ℝ)*budget X A K n t := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hUR : (0 : ℝ) < ((A*K : ℕ) : ℝ) := by exact_mod_cast (Nat.mul_pos hA hK)
  have hT : 0 < |t| := abs_pos.mpr ht
  have hFact : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hPositive : ∀ h ∈ hs, 0 < h := fun h hh ↦ hAR.trans_le (hhs h hh).1
  have hNN : ∀ h ∈ hs, 0 ≤ h := fun h hh ↦ (hPositive h hh).le
  have hSumNN := ReciprocalDifferenceBounds.shifts_sum_nonneg hs hNN
  have hSum := sum_upper hs ((A*K : ℕ) : ℝ) (fun h hh ↦ (hhs h hh).2)
  rw [hLen] at hSum
  have hSumX : hs.sum ≤ (X : ℝ) := hSum.trans (by exact_mod_cast hSpan)
  have hProd := product_bounds hs (A : ℝ) ((A*K : ℕ) : ℝ) hAR.le hUR.le hhs
  rw [hLen] at hProd
  have hProdPos : 0 < hs.prod := (pow_pos hAR n).trans_le hProd.1
  have hLXR : (L : ℝ) ≤ X := by exact_mod_cast hLX
  have hEndpoint : (((X+L : ℕ) : ℝ)+hs.sum) ≤ 3*(X : ℝ) := by
    push_cast
    linarith only [hSumX,hLXR]
  have hEndpointNN : 0 ≤ (((X+L : ℕ) : ℝ)+hs.sum) := by positivity
  have hBound := IteratedLogarithmicSum.integer_sum_bound hs hPositive X (X+L) hX (by omega) t ht
  rw [hLen] at hBound
  simp only [Nat.add_sub_cancel_left] at hBound
  have hFirst : 2*(((X+L : ℕ) : ℝ)+hs.sum)^(n+1)/(|t| * (n.factorial : ℝ)*hs.prod) ≤
      2*(3*(X : ℝ))^(n+1)/(|t| * (n.factorial : ℝ)*(A : ℝ)^n) := by
    have hPow := pow_le_pow_left₀ hEndpointNN hEndpoint (n+1)
    have hDen := mul_le_mul_of_nonneg_left hProd.1 (show 0 ≤ |t| * (n.factorial : ℝ) by positivity)
    calc
      _ ≤ 2*(3*(X : ℝ))^(n+1)/(|t| * (n.factorial : ℝ)*hs.prod) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hPow (by norm_num : (0 : ℝ) ≤ 2)) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hDen
  have hSecond : (L : ℝ)*(|t| * ((n.factorial : ℝ)*hs.prod)/(X : ℝ)^(n+1)) ≤
      (X : ℝ)*(|t| * ((n.factorial : ℝ)*((A*K : ℕ) : ℝ)^n)/(X : ℝ)^(n+1)) := by
    have hNum := mul_le_mul_of_nonneg_left hProd.2 (show 0 ≤ |t| * (n.factorial : ℝ) by positivity)
    have hDiv : |t| * ((n.factorial : ℝ)*hs.prod)/(X : ℝ)^(n+1) ≤
        |t| * ((n.factorial : ℝ)*((A*K : ℕ) : ℝ)^n)/(X : ℝ)^(n+1) := by
      simpa only [mul_assoc] using div_le_div_of_nonneg_right hNum (pow_nonneg hXR.le (n+1))
    have hScalar : 0 ≤ |t| * ((n.factorial : ℝ)*hs.prod)/(X : ℝ)^(n+1) := by positivity
    have hh := mul_le_mul hLXR hDiv hScalar (Nat.cast_nonneg X : (0 : ℝ) ≤ X)
    exact hh
  exact hBound.trans ((add_le_add hFirst hSecond).trans_eq (by
    simp only [budget,mul_pow,pow_succ]
    ring))

theorem logarithmic_bound (X A K n : ℕ) (hX : 0 < X) (hA : 0 < A) (hK : 0 < K)
    (hAK : A*K ≤ X) (hSpan : n*(A*K) ≤ X) (t : ℝ) (ht : t ≠ 0) :
    ‖∑ j ∈ Ico X (2*X), LogarithmicExponentialSum.function t j‖ ≤
      (X : ℝ)*RecursiveLogarithmicDifferencing.budget K n (budget X A K n t) := by
  apply RecursiveLogarithmicDifferencing.logarithmic_bound X A K hA hK hAK t
    (budget X A K n t) (budget_nonneg X A K n t) n
  intro hs hLen hhs L hLX
  exact leaf_bound X A K n hX hA hK hSpan t ht hs hLen hhs L hLX
end PaperP1.TerminalLogarithmicBudget
