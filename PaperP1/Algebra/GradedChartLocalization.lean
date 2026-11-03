module

public import PaperP1.Algebra.GradedDehomogenization
public import Mathlib.RingTheory.Localization.Away.Basic

/-! # A bijective homogeneous chart map induces a bijection on the full localized rings

The statement includes zero divisors. Kernel elements are killed by a power
of the chart coordinate; surjectivity clears denominators component by component.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedChartLocalization

open HomogeneousLocalization DirectSum

variable {A B : Type*} [CommRing A] [CommRing B]

theorem clear_add (f : A →+* B) (b : A) {x y : B}
    (hx : ∃ a m, f a = f b ^ m * x) (hy : ∃ a m, f a = f b ^ m * y) :
    ∃ a m, f a = f b ^ m * (x + y) := by
  obtain ⟨a, m, ha⟩ := hx
  obtain ⟨c, n, hc⟩ := hy
  refine ⟨b ^ n * a + b ^ m * c, m + n, ?_⟩
  rw [map_add, map_mul, map_mul, map_pow, map_pow, ha, hc, pow_add]
  ring

theorem clear_sum {ι : Type*} (f : A →+* B) (b : A) (s : Finset ι) (x : ι → B)
    (hx : ∀ i ∈ s, ∃ a m, f a = f b ^ m * x i) :
    ∃ a m, f a = f b ^ m * ∑ i ∈ s, x i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, by simp⟩
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact clear_add f b (hx i (Finset.mem_insert_self i s))
        (ih (fun j hj ↦ hx j (Finset.mem_insert_of_mem hj)))

variable {σ τ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B] {G : ℕ → σ} {H : ℕ → τ}
  [GradedRing G] [GradedRing H]
  (f : G →+*ᵍ H) {b : A} (hb : b ∈ G 1)

include hb in
theorem map_injective (hf : Function.Injective (Away.map f b)) :
    Function.Injective (Localization.awayMap f.toRingHom b) := by
  classical
  apply Localization.awayMap_injective_iff.mpr
  intro x hx
  change f x = 0 at hx
  have hloc : algebraMap A (Localization.Away b) x = 0 := by
    rw [← sum_support_decompose G x, map_sum]
    apply Finset.sum_eq_zero
    intro n _hn
    have hfn : f (decompose G x n) = 0 := by
      rw [f.map_directSumDecompose, hx]
      simp
    have hd : GradedDehomogenization.map G hb (decompose G x n) = 0 := by
      apply hf
      rw [map_zero]
      have h := DFunLike.congr_fun (GradedDehomogenization.map_natural G hb f) (decompose G x n : A)
      simpa only [RingHom.comp_apply, GradedRingHom.coe_toRingHom, hfn, map_zero] using h
    rw [GradedDehomogenization.map_homogeneous G hb n _ (decompose G x n).property] at hd
    have hv := congrArg HomogeneousLocalization.val hd
    simp only [Away.val_mk, val_zero, Localization.mk_eq_mk'] at hv
    exact (IsLocalization.map_eq_zero_iff (Submonoid.powers b) (Localization.Away b) _).mpr
      ((IsLocalization.mk'_eq_zero_iff _ _).mp hv)
  obtain ⟨⟨u, m, rfl⟩, hm⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers b) (Localization.Away b) x).mp hloc
  exact ⟨m, hm⟩

include hb in
theorem homogeneous_clear_degree (hf : Function.Surjective (Away.map f b)) (n : ℕ) (y : B) (hy : y ∈ H n) :
    ∃ a m, a ∈ G (m + n) ∧ f a = f b ^ m * y := by
  obtain ⟨z, hz⟩ := hf (GradedDehomogenization.map H (f.map_mem hb) y)
  obtain ⟨m, a, ha, rfl⟩ := Away.mk_surjective G hb z
  rw [Away.map_mk, GradedDehomogenization.map_homogeneous H (f.map_mem hb) n y hy] at hz
  have hv := congrArg HomogeneousLocalization.val hz
  simp only [Away.val_mk, Localization.mk_eq_mk'] at hv
  obtain ⟨⟨u, t, rfl⟩, ht⟩ := (IsLocalization.eq (S := Localization.Away (f b))).mp hv
  refine ⟨b ^ (t + n) * a, t + m, ?_, ?_⟩
  · have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded (t + n) hb) ha
    simpa only [smul_eq_mul, mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  · rw [map_mul, map_pow, pow_add, pow_add]
    simpa only [GradedRingHom.coe_toRingHom, mul_assoc] using ht

include hb in
theorem homogeneous_clear (hf : Function.Surjective (Away.map f b)) (n : ℕ) (y : B) (hy : y ∈ H n) :
    ∃ a m, f a = f b ^ m * y := by
  obtain ⟨a, m, _, ha⟩ := homogeneous_clear_degree f hb hf n y hy
  exact ⟨a, m, ha⟩

include hb in
theorem map_surjective (hf : Function.Surjective (Away.map f b)) :
    Function.Surjective (Localization.awayMap f.toRingHom b) := by
  classical
  apply Localization.awayMap_surjective_iff.mpr
  intro y
  rw [← sum_support_decompose H y]
  apply clear_sum f.toRingHom b
  intro n _hn
  exact homogeneous_clear f hb hf n _ (decompose H y n).property

def equiv (hf : Function.Bijective (Away.map f b)) :
    Localization.Away b ≃+* Localization.Away (f b) :=
  RingEquiv.ofBijective (Localization.awayMap f.toRingHom b)
    ⟨map_injective f hb hf.1, map_surjective f hb hf.2⟩

end PaperP1.GradedChartLocalization
