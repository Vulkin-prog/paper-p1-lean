module

public import PaperP1.Arithmetic.ReceivedPrimeCertificate

/-! # A private anchor prime in a literal parity relation is received elsewhere -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateOffsetPrimeReceivers

open Finset PaperP1.Arithmetic PaperP1.LinearKernelFibres
  PaperP1.LargeOddKernel PaperP1.TruncatedKernelProducts

theorem values_ne (x W : ℕ) (a b : ℤ) (hx : W < x)
    (ha : a.natAbs ≤ W) (hb : b.natAbs ≤ W) (hab : a ≠ b) : value x a ≠ value x b := by
  intro heq
  have hcast := congrArg (fun n : ℕ ↦ (n : ℤ)) heq
  rw [PaperP1.SmoothModulusHosts.value_cast x W a hx ha,
    PaperP1.SmoothModulusHosts.value_cast x W b hx hb] at hcast
  exact hab (by omega)

theorem values_dist (x W : ℕ) (a b : ℤ) (hx : W < x)
    (ha : a.natAbs ≤ W) (hb : b.natAbs ≤ W) : Nat.dist (value x a) (value x b) ≤ 2 * W := by
  have hva := PaperP1.SmoothModulusHosts.value_cast x W a hx ha
  have hvb := PaperP1.SmoothModulusHosts.value_cast x W b hx hb
  have haa : |a| ≤ (W : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast ha
  have hbb : |b| ≤ (W : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hb
  have hal := abs_le.mp haa
  have hbl := abs_le.mp hbb
  rcases le_total (value x a) (value x b) with h | h
  · rw [Nat.dist_eq_sub_of_le h]; omega
  · rw [Nat.dist_eq_sub_of_le_right h]; omega

theorem not_dvd_other (x W p : ℕ) (a b : ℤ) (hx : W < x)
    (ha : a.natAbs ≤ W) (hb : b.natAbs ≤ W) (hab : a ≠ b)
    (hp : 2 * W < p) (hdiv : p ∣ value x a) : ¬p ∣ value x b := by
  intro hother
  have hdist := values_dist x W a b hx ha hb
  have hne := values_ne x W a b hx ha hb hab
  have hdivdist : p ∣ Nat.dist (value x a) (value x b) := by
    rcases le_total (value x a) (value x b) with h | h
    · rw [Nat.dist_eq_sub_of_le h]
      exact Nat.dvd_sub hother hdiv
    · rw [Nat.dist_eq_sub_of_le_right h]
      exact Nat.dvd_sub hdiv hother
  have hple := Nat.le_of_dvd (Nat.dist_pos_of_ne hne) hdivdist
  omega

theorem other_receiver {ρ : Type*} [Fintype ρ]
    (x W : ℕ) (z : ρ → ℕ) (S : Finset ℤ) (T : ρ → Finset ℤ) (a : ℤ) (Y : ℝ) (p : ℕ)
    (hx : W < x) (hS : ∀ u ∈ S, u.natAbs ≤ W) (ha : a ∈ S)
    (hY : (2 * W : ℝ) ≤ Y)
    (hp : p ∈ support Y (value x a))
    (hrelation : (∑ u ∈ S, parityVec (value x u)) + (∑ j, ∑ v ∈ T j, parityVec (value (z j) v)) = 0) :
    ∃ j : ρ, ∃ v ∈ T j, p ∣ value (z j) v := by
  classical
  have hpodd := (mem_filter.mp hp).1
  have hYp := (mem_filter.mp hp).2
  have hpi := mem_oddPrimeSupport_iff_parityVec_ne_zero.mp hpodd
  have hpdiv := dvd_of_mem_oddPrimeSupport hpodd
  have hpW : 2 * W < p := by exact_mod_cast hY.trans_lt hYp
  by_contra hnone
  have hnot : ∀ j : ρ, ∀ v ∈ T j, ¬p ∣ value (z j) v := by
    intro j v hv hd
    exact hnone ⟨j, v, hv, hd⟩
  have hsecond : (∑ j, ∑ v ∈ T j, parityVec (value (z j) v) p) = 0 := by
    apply sum_eq_zero
    intro j _
    apply sum_eq_zero
    intro v hv
    simp only [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd (hnot j v hv), Nat.cast_zero]
  have hfirst : (∑ u ∈ S, parityVec (value x u) p) = parityVec (value x a) p := by
    apply sum_eq_single a
    · intro u hu hua
      have hnodiv := not_dvd_other x W p a u hx (hS a ha) (hS u hu) hua.symm hpW hpdiv
      simp only [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd hnodiv, Nat.cast_zero]
    · exact fun hnot ↦ (hnot ha).elim
  have hcoord := congrArg (fun v : ℕ →₀ F₂ ↦ v p) hrelation
  simp only [Finsupp.add_apply, Finsupp.finsetSum_apply, Finsupp.zero_apply] at hcoord
  rw [hfirst, hsecond, add_zero] at hcoord
  exact hpi hcoord

end PaperP1.PrivateOffsetPrimeReceivers
