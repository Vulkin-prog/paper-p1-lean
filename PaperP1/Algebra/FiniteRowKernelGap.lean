module

public import PaperP1.Algebra.FiniteRowKernel

/-! # A fixed-power integer annihilator from the actual row-rank gap

A fixed positive fraction of free coefficient dimensions avoids the
dimension-sized exponent in the older codimension-one interpolation bound.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteRowKernelGap

open Finset Submodule

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
theorem exists_rank_spanning_rows (A : ι → κ → ℚ) :
    ∃ r : ℕ, r = Module.finrank ℚ (span ℚ (Set.range A)) ∧ ∃ f : Fin r → ι,
      span ℚ (Set.range (A ∘ f)) = span ℚ (Set.range A) := by
  classical
  obtain ⟨γ, f, hf, hspan, hli⟩ := exists_linearIndependent' ℚ A
  let : Finite γ := Finite.of_injective f hf
  let : Fintype γ := Fintype.ofFinite γ
  let e : γ ≃ Fin (Fintype.card γ) := Fintype.equivFin γ
  have hdim : Fintype.card γ = Module.finrank ℚ (span ℚ (Set.range A)) := by
    rw [← hspan]
    exact (Module.finrank_eq_card_basis (Module.Basis.span hli)).symm
  refine ⟨Fintype.card γ, hdim, fun i ↦ f (e.symm i), ?_⟩
  have hrange : Set.range (A ∘ (fun i ↦ f (e.symm i))) = Set.range (A ∘ f) := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e i, by simp⟩
  rw [hrange]
  exact hspan

theorem exists_integer_annihilator (H : ℕ) (hH : 0 < H) (hn : 0 < Fintype.card κ)
    (A : ι → κ → ℤ) (hA : ∀ i j, |A i j| ≤ (H : ℤ))
    (hrank : 8 * Module.finrank ℚ (span ℚ (Set.range (fun i j ↦ (A i j : ℚ)))) ≤
      7 * Fintype.card κ) :
    ∃ w : κ → ℤ, w ≠ 0 ∧ (∀ j, |w j| ≤ ((3 * Fintype.card κ * H) ^ 7 : ℕ)) ∧
      ∀ i, ∑ j, A i j * w j = 0 := by
  classical
  let v : ι → κ → ℚ := fun i j ↦ A i j
  obtain ⟨r, hr, f, hspan⟩ := exists_rank_spanning_rows v
  have hdim : 8 * r ≤ 7 * Fintype.card κ := by rw [hr]; exact hrank
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  obtain ⟨u, hu0, hu, hzero⟩ := SmallIntegerKernel.exists_small_kernel H hn hH hdim
    (fun i j ↦ A (f i) (e.symm j)) (fun i j ↦ hA (f i) (e.symm j))
  let w : κ → ℤ := fun j ↦ u (e j)
  have hw0 : w ≠ 0 := by
    intro hz
    apply hu0
    funext j
    simpa only [w, e.apply_symm_apply, Pi.zero_apply] using congrFun hz (e.symm j)
  have hselectedZero (i : Fin r) : ∑ j, A (f i) j * w j = 0 := by
    calc
      _ = ∑ j, A (f i) (e.symm j) * u j :=
        Fintype.sum_equiv e _ _ (fun j ↦ by dsimp only [w]; rw [e.symm_apply_apply])
      _ = 0 := hzero i
  let L : (κ → ℚ) →ₗ[ℚ] ℚ := Fintype.linearCombination ℚ (fun j ↦ (w j : ℚ))
  have hsub : span ℚ (Set.range (v ∘ f)) ≤ LinearMap.ker L := by
    apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (∑ j, (A (f i) j : ℚ) • (w j : ℚ)) = 0
    simp only [smul_eq_mul]
    exact_mod_cast hselectedZero i
  rw [hspan] at hsub
  refine ⟨w, hw0, fun j ↦ hu (e j), ?_⟩
  intro i
  have hi := hsub (subset_span (Set.mem_range_self i))
  change (∑ j, (A i j : ℚ) • (w j : ℚ)) = 0 at hi
  simp only [smul_eq_mul] at hi
  exact_mod_cast hi

end PaperP1.FiniteRowKernelGap
