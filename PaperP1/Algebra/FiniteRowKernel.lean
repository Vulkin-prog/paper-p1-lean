module

public import PaperP1.Algebra.SmallIntegerKernelRankGap
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Singular square row minors give a bounded integer annihilator of the entire finite family -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteRowKernel

open Finset Submodule

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem exists_spanning_rows (A : ι → κ → ℚ)
    (hminor : ∀ f : κ → ι, (Matrix.of (fun i j ↦ A (f i) j)).det = 0) :
    ∃ r : ℕ, r < Fintype.card κ ∧ ∃ f : Fin r → ι,
      span ℚ (Set.range (A ∘ f)) = span ℚ (Set.range A) := by
  classical
  obtain ⟨γ, f, hf, hspan, hli⟩ := exists_linearIndependent' ℚ A
  let : Finite γ := Finite.of_injective f hf
  let : Fintype γ := Fintype.ofFinite γ
  have hle := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at hle
  have hlt : Fintype.card γ < Fintype.card κ := by
    by_contra h
    have heq : Fintype.card κ = Fintype.card γ := by omega
    let e : κ ≃ γ := Fintype.equivOfCardEq heq
    let M : Matrix κ κ ℚ := Matrix.of (fun i j ↦ A (f (e i)) j)
    have hi : LinearIndependent ℚ M.row := by
      change LinearIndependent ℚ (fun i ↦ A (f (e i)))
      simpa only [Function.comp_def] using hli.comp e e.injective
    have hunit : IsUnit M := Matrix.linearIndependent_row_iff_isUnit.mp hi
    have hdet : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det M).mp hunit).ne_zero
    exact hdet (hminor (fun i ↦ f (e i)))
  let e : γ ≃ Fin (Fintype.card γ) := Fintype.equivFin γ
  refine ⟨Fintype.card γ, hlt, fun i ↦ f (e.symm i), ?_⟩
  have hrange : Set.range (A ∘ (fun i ↦ f (e.symm i))) = Set.range (A ∘ f) := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e i, by simp⟩
  rw [hrange]
  exact hspan

theorem exists_integer_annihilator (nH : ℕ) (hnH : 0 < nH) (hn : 0 < Fintype.card κ)
    (A : ι → κ → ℤ) (hA : ∀ i j, |A i j| ≤ (nH : ℤ))
    (hminor : ∀ f : κ → ι, (Matrix.of (fun i j ↦ (A (f i) j : ℚ))).det = 0) :
    ∃ w : κ → ℤ, w ≠ 0 ∧
      (∀ j, |w j| ≤ ((3 * Fintype.card κ * nH) ^ (Fintype.card κ - 1) : ℕ)) ∧
        ∀ i, ∑ j, A i j * w j = 0 := by
  classical
  let v : ι → κ → ℚ := fun i j ↦ A i j
  obtain ⟨r, hr, f, hspan⟩ := exists_spanning_rows v hminor
  obtain ⟨w, hw0, hw, hzero⟩ := SmallIntegerKernelRankGap.exists_uniform_small_kernel_equiv
    (Fintype.card κ) r nH hn hnH hr (Fintype.equivFin κ)
    (fun i j ↦ A (f i) j) (fun i j ↦ hA (f i) j)
  let L : (κ → ℚ) →ₗ[ℚ] ℚ := Fintype.linearCombination ℚ (fun j ↦ (w j : ℚ))
  have hselected (i : Fin r) : v (f i) ∈ LinearMap.ker L := by
    change (∑ j, (A (f i) j : ℚ) • (w j : ℚ)) = 0
    simp only [smul_eq_mul]
    exact_mod_cast hzero i
  have hsub : span ℚ (Set.range (v ∘ f)) ≤ LinearMap.ker L := by
    apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hselected i
  rw [hspan] at hsub
  refine ⟨w, hw0, hw, ?_⟩
  intro i
  have hi := hsub (subset_span (Set.mem_range_self i))
  change (∑ j, (A i j : ℚ) • (w j : ℚ)) = 0 at hi
  simp only [smul_eq_mul] at hi
  exact_mod_cast hi

end PaperP1.FiniteRowKernel
