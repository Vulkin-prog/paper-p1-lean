module

public import PaperP1.Arithmetic.DeterminantLocalChart
public import PaperP1.Asymptotics.DeterminantBoundedAuxiliaryHeight

/-! # Actual bounded auxiliary curves from local source data, without a minor hypothesis -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalDeterminantAuxiliary

open Finset PaperP1.DeterminantIntegerRows PaperP1.TwoKernelDeterminantBoxes
  PaperP1.DeterminantLocalChart PaperP1.ActualRelativeDeterminant PaperP1.DeterminantAuxiliaryBiform

structure Points {T δ C W η : ℝ} (D : Data T δ C W η) (S : Finset Quad) (Q N : ℕ) : Prop where
  height : ∀ p ∈ S, p.1.1 ≤ Q * N ∧ p.1.2 ≤ Q * N ∧ p.2.1 ≤ Q * N ∧ p.2.2 ≤ Q * N
  e_pos : ∀ p ∈ S, 0 < p.1.2
  u_pos : ∀ p ∈ S, 0 < p.2.1
  e_bound : ∀ p ∈ S, (p.1.2 : ℝ) ≤ D.E
  u_bound : ∀ p ∈ S, (p.2.1 : ℝ) ≤ D.U
  equation : ∀ p ∈ S, D.c₂ * (p.1.2 : ℝ) ^ 2 * p.2.2 = D.c₁ * (p.1.1 : ℝ) ^ 2 * p.2.1 + D.h
  horizontal : ∀ p ∈ S, |relativeAlpha D.s₀ p| ≤ Real.exp (-(D.σ * T))
  vertical : ∀ p ∈ S, |relativeError D.c₁ D.c₂ D.h D.s₀ p| ≤ Real.exp (-(D.τ * T))

theorem uniform_coefficients (δ C W η : ℝ) (hδ : 0 < δ) (hη : 0 < η)
    (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ B Amax κ N₀ : ℕ, 0 < B ∧ ∀ N ≥ N₀, ∀ D : Data (Real.log N) δ C W η,
      ∃ A : ℕ, 0 < A ∧ A ≤ Amax ∧ ∀ S : Finset Quad, Points D S Q N →
        ∃ w : Exponent A B → ℤ, w ≠ 0 ∧ (∀ i, |w i| ≤ ((N ^ κ : ℕ) : ℤ)) ∧
          ∀ p ∈ S, (∑ i, (w i : ℚ) * rationalEntry A B p i) = 0 := by
  obtain ⟨B, Amax, T₀, hB, hT₀, hchoice⟩ :=
    DeterminantUniformMargin.uniform_degrees_and_threshold δ C W η hδ hη
  obtain ⟨κ, Nh, hheight⟩ := DeterminantBoundedAuxiliaryHeight.uniform_coefficients Amax B Q hQ
  let N₀ := max 2 (max Nh ⌈Real.exp T₀⌉₊)
  refine ⟨B, Amax, κ, N₀, hB, ?_⟩
  intro N hN D
  have hN₂ : 2 ≤ N := by dsimp [N₀] at hN; omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hT : T₀ ≤ Real.log N := by
    apply (Real.le_log_iff_exp_le hNpos).mpr
    exact (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈Real.exp T₀⌉₊ ≤ N by dsimp [N₀] at hN; omega))
  obtain ⟨A, hA₀, hA, hmargin, hconstant⟩ := hchoice (Real.log N) hT D.a D.b D.σ D.τ
    D.first_lower D.first_upper D.second_lower D.second_upper D.horizontal_pos D.vertical_pos
    D.weight_sum D.weight_product
  refine ⟨A, hA₀, hA, ?_⟩
  intro S hS
  apply hheight N (by dsimp [N₀] at hN; omega) A hA S hS.height hS.e_pos hS.u_pos
  exact minors_small D (hT₀.trans_le hT) A B hmargin hconstant S hS.e_pos hS.u_pos
    hS.e_bound hS.u_bound hS.equation hS.horizontal hS.vertical

theorem uniform_biform (δ C W η : ℝ) (hδ : 0 < δ) (hη : 0 < η)
    (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ B Amax κ N₀ : ℕ, 0 < B ∧ ∀ N ≥ N₀, ∀ D : Data (Real.log N) δ C W η,
      ∃ A : ℕ, 0 < A ∧ A ≤ Amax ∧ ∀ S : Finset Quad, Points D S Q N →
        ∃ w : Exponent A B → ℤ, biform A B w ≠ 0 ∧
          (biform A B w).IsHomogeneous A ∧ (∀ a, (forms A B w a).IsHomogeneous B) ∧
          (∀ m n, |((biform A B w).coeff m).coeff n| ≤ ((N ^ κ : ℕ) : ℤ)) ∧
          ∀ p ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval ![(p.2.2 : ℤ), p.2.1])
            ![(p.1.1 : ℤ), p.1.2] (biform A B w) = 0 := by
  obtain ⟨B, Amax, κ, N₀, hB, h⟩ := uniform_coefficients δ C W η hδ hη Q hQ
  refine ⟨B, Amax, κ, N₀, hB, ?_⟩
  intro N hN D
  obtain ⟨A, hA₀, hA, hcoeff⟩ := h N hN D
  refine ⟨A, hA₀, hA, ?_⟩
  intro S hS
  obtain ⟨w, hw₀, hw, hzero⟩ := hcoeff S hS
  exact ⟨w, biform_nonzero A B w hw₀, biform_homogeneous A B w,
    forms_homogeneous A B w, biform_coefficient_bound A B (N ^ κ) w hw,
    fun p hp ↦ biform_zero_of_rational_zero A B w p (hS.e_pos p hp) (hS.u_pos p hp) (hzero p hp)⟩

end PaperP1.LocalDeterminantAuxiliary
