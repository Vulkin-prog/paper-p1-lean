module

public import PaperP1.Algebra.GradedDehomogenizationQuotient
public import Lean.Elab.Tactic.Omega

/-! # Degree-one chart representatives can be chosen in prescribed large homogeneous degrees -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedDehomogenizationPieces

open HomogeneousLocalization

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (G : ℕ → σ) [GradedRing G] {b : A} (hb : b ∈ G 1)

include hb in
theorem homogeneous_eq_zero [IsDomain A] (hb0 : b ≠ 0) (n : ℕ) {x : A} (hx : x ∈ G n)
    (h : GradedDehomogenization.map G hb x = 0) : x = 0 := by
  rw [GradedDehomogenization.map_homogeneous G hb n x hx] at h
  have hv := congrArg HomogeneousLocalization.val h
  simp only [Away.val_mk, val_zero, Localization.mk_eq_mk'] at hv
  obtain ⟨t, ht⟩ := (IsLocalization.mk'_eq_zero_iff (S := Localization.Away b) x _).mp hv
  have ht0 : (t : A) ≠ 0 := by
    obtain ⟨r, hr⟩ := t.property
    rw [← hr]
    exact pow_ne_zero r hb0
  exact (mul_eq_zero.mp ht).resolve_left ht0

theorem lift_large_degree (z : Away G b) :
    ∃ m : ℕ, ∀ n : ℕ, m ≤ n → ∃ a : A, a ∈ G n ∧ GradedDehomogenization.map G hb a = z := by
  obtain ⟨m, a, ha, rfl⟩ := Away.mk_surjective G hb z
  have ha' : a ∈ G m := by simpa only [smul_eq_mul, mul_one] using ha
  refine ⟨m, fun n hn ↦ ⟨a * b ^ (n - m), ?_, ?_⟩⟩
  · have hm : a * b ^ (n - m) ∈ G (m + (n - m)) := by
      simpa only [smul_eq_mul, mul_one] using
        SetLike.mul_mem_graded ha' (SetLike.pow_mem_graded (n - m) hb)
    simpa only [Nat.add_sub_of_le hn] using hm
  · rw [map_mul, map_pow, GradedDehomogenizationQuotient.map_variable G hb, one_pow, mul_one]
    exact GradedDehomogenization.map_homogeneous G hb m a ha'

theorem lift_finite_weighted {ι : Type*} [Fintype ι] (z : ι → Away G b) (w : ι → ℕ) :
    ∃ N : ℕ, (∀ i, w i ≤ N) ∧ ∀ i, ∃ a : A, a ∈ G (N - w i) ∧
      GradedDehomogenization.map G hb a = z i := by
  classical
  choose k hk using fun i ↦ lift_large_degree G hb (z i)
  let N := Finset.univ.sup (fun i ↦ k i + w i)
  have hN (i : ι) : k i + w i ≤ N := Finset.le_sup (f := fun i ↦ k i + w i) (Finset.mem_univ i)
  refine ⟨N, fun i ↦ ?_, fun i ↦ hk i (N - w i) ?_⟩ <;> have := hN i <;> omega

end PaperP1.GradedDehomogenizationPieces
