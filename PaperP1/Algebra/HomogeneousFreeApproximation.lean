module

public import PaperP1.Algebra.FiniteGradedModuleSandwich

/-! # A finite homogeneous module family admits a homogeneous common denominator -/

set_option autoImplicit false

@[expose] public noncomputable section

open scoped Classical

namespace PaperP1.HomogeneousFreeApproximation

open Finset DirectSum

variable {F A B ι : Type*} [Field F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B] [Fintype ι]
  {G : ℕ → Submodule F A} {H : ℕ → Submodule F B}
  [GradedAlgebra G] [GradedAlgebra H]
  (f : G →+*ᵍ H) (v : ι → B) (w : ι → ℕ) (hv : ∀ i, v i ∈ H (w i))

include hv in
theorem component_mul_mem_span (q : A)
    (hclear : ∀ b : B, ∃ a : ι → A, ∑ i, f (a i) * v i = f q * b)
    (m n : ℕ) {b : B} (hb : b ∈ H n) :
    letI : Algebra A B := f.toRingHom.toAlgebra
    f (decompose G q m) * b ∈ Submodule.span A (Set.range v) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let S := Submodule.span A (Set.range v)
  obtain ⟨a, ha⟩ := hclear b
  have he := congrArg (fun x ↦ GradedAlgebra.proj H (n + m) x) ha
  rw [map_sum] at he
  have hs : (∑ i, GradedAlgebra.proj H (n + m) (f (a i) * v i)) ∈ S := by
    apply S.sum_mem
    intro i _
    rw [GradedAlgebra.proj_apply]
    by_cases hi : w i ≤ n + m
    · rw [coe_decompose_mul_of_right_mem_of_le H (hv i) hi, ← f.map_directSumDecompose]
      exact S.smul_mem (decompose G (a i) (n + m - w i) : A) (Submodule.subset_span ⟨i, rfl⟩)
    · rw [coe_decompose_mul_of_right_mem_of_not_le H (hv i) hi]
      exact S.zero_mem
  have hright : GradedAlgebra.proj H (n + m) (f q * b) = f (decompose G q m) * b := by
    rw [GradedAlgebra.proj_apply, Nat.add_comm n m, coe_decompose_mul_add_of_right_mem H hb,
      ← f.map_directSumDecompose]
  exact he.trans hright ▸ hs

include hv in
theorem component_clears (q : A)
    (hclear : ∀ b : B, ∃ a : ι → A, ∑ i, f (a i) * v i = f q * b)
    (m : ℕ) : ∀ b : B, ∃ a : ι → A, ∑ i, f (a i) * v i = f (decompose G q m) * b := by
  let : Algebra A B := f.toRingHom.toAlgebra
  intro b
  apply (Submodule.mem_span_range_iff_exists_fun A).mp
  rw [← sum_support_decompose H b, Finset.mul_sum]
  apply Submodule.sum_mem
  intro n _
  exact component_mul_mem_span f v w hv q hclear m n (decompose H b n).property

include hv in
theorem exists_homogeneous_free_approximation [IsDomain A]
    (hgen : letI : Algebra A B := f.toRingHom.toAlgebra
      Submodule.span A (Set.range v) = ⊤) :
    ∃ (s : Finset ι) (m : ℕ) (q : A), q ∈ G m ∧ q ≠ 0 ∧
      (letI : Algebra A B := f.toRingHom.toAlgebra;
        LinearIndependent A (fun i : s ↦ v i)) ∧
      ∀ b : B, ∃ a : s → A, ∑ i, f (a i) * v i = f q * b := by
  obtain ⟨s, q, hq, hli, hclear⟩ := FiniteGradedModuleSandwich.exists_free_approximation f v hgen
  obtain ⟨m, hm⟩ := HomogeneousDenominator.exists_component_ne_zero (G := G) hq
  exact ⟨s, m, decompose G q m, (decompose G q m).property, hm, hli,
    component_clears f (fun i : s ↦ v i) (fun i : s ↦ w i) (fun i ↦ hv i) q hclear m⟩

end PaperP1.HomogeneousFreeApproximation
