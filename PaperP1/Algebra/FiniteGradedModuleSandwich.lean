module

public import PaperP1.Algebra.HomogeneousDenominator
public import PaperP1.Algebra.FreeApproximationRank
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! # Genuine homogeneous free approximations of a finite graded algebra module -/

set_option autoImplicit false

@[expose] public noncomputable section

open scoped Classical

namespace PaperP1.FiniteGradedModuleSandwich

open Finset DirectSum

variable {F A B ι : Type*} [Field F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B] [Fintype ι]
  {G : ℕ → Submodule F A} {H : ℕ → Submodule F B}
  [GradedAlgebra G] [GradedAlgebra H]
  (f : G →+*ᵍ H) (hscalar : ∀ a : F, f (algebraMap F A a) = algebraMap F B a)
  (v : ι → B) (w : ι → ℕ) (hv : ∀ i, v i ∈ H (w i))

omit [GradedAlgebra G] [GradedAlgebra H] in
theorem exists_free_approximation [IsDomain A]
    (hgen : letI : Algebra A B := f.toRingHom.toAlgebra
      Submodule.span A (Set.range v) = ⊤) :
    ∃ (s : Finset ι) (q : A), q ≠ 0 ∧
      (letI : Algebra A B := f.toRingHom.toAlgebra;
        LinearIndependent A (fun i : s ↦ v i)) ∧
      ∀ b : B, ∃ a : s → A, ∑ i, f (a i) * v i = f q * b := by
  let : Algebra A B := f.toRingHom.toAlgebra
  obtain ⟨s, hs, q, hq, hclear⟩ := exists_linearIndepOn_smul_mem_span hgen
  let : Fintype s := Fintype.ofFinite _
  let t : Finset ι := s.toFinset
  have ht : (t : Set ι) = s := Set.coe_toFinset s
  refine ⟨t, q, hq, ?_, fun b ↦ ?_⟩
  · change LinearIndepOn A v (t : Set ι)
    rw [ht]
    exact hs
  · have hb : f q * b ∈ Submodule.span A (Set.range fun i : t ↦ v i) := by
      change f q * b ∈ Submodule.span A (Set.range fun i : (t : Set ι) ↦ v i)
      rw [← Set.image_eq_range v (t : Set ι), ht]
      exact hclear b
    exact (Submodule.mem_span_range_iff_exists_fun A).mp hb

include hscalar hv in
theorem exists_sandwich [IsDomain A] [IsDomain B] (hinj : Function.Injective f)
    (hgen : letI : Algebra A B := f.toRingHom.toAlgebra
      Submodule.span A (Set.range v) = ⊤)
    (hfin : ∀ n : ℕ, Module.Finite F (G n)) :
    ∃ (s : Finset ι) (m N : ℕ),
      (letI : Algebra A B := f.toRingHom.toAlgebra; s.card = Module.finrank A B) ∧
      ∀ n : ℕ, N ≤ n →
      Module.Finite F (H n) ∧
      (∑ i : s, Module.finrank F (G (n - w i))) ≤ Module.finrank F (H n) ∧
      Module.finrank F (H n) ≤ ∑ i : s, Module.finrank F (G (n + m - w i)) := by
  obtain ⟨s, q, hq, hli, hclear⟩ := exists_free_approximation f v hgen
  let : Algebra A B := f.toRingHom.toAlgebra
  have : Module.Finite A B := FreeApproximationRank.finite_of_span v hgen
  have hcard : s.card = Module.finrank A B := by
    have hc := FreeApproximationRank.finrank_eq (fun i : s ↦ v i) hinj hli q hq (fun b ↦ by
      apply (Submodule.mem_span_range_iff_exists_fun A).mpr
      exact hclear b)
    simpa only [Fintype.card_coe] using hc.symm
  obtain ⟨m, hm⟩ := HomogeneousDenominator.exists_component_ne_zero (G := G) hq
  let N := univ.sup w
  have hnweight (n : ℕ) (hn : N ≤ n) (i : s) : w i ≤ n :=
    (Finset.le_sup (f := w) (Finset.mem_univ (i : ι))).trans hn
  refine ⟨s, m, N, hcard, fun n hn ↦ ?_⟩
  have hnf : ∀ i : s, Module.Finite F (G (n + m - w i)) := fun i ↦ hfin _
  let := hnf
  have hH : Module.Finite F (H n) := HomogeneousDenominator.piece_finite f hscalar
    (fun i : s ↦ v i) (fun i : s ↦ w i) (fun i ↦ hv i) hinj q hclear m hm n
      (fun i ↦ (hnweight n hn i).trans (Nat.le_add_right n m))
  refine ⟨hH, ?_, ?_⟩
  · exact GradedModulePieceMap.finrank_ge f hscalar
      (fun i : s ↦ v i) (fun i : s ↦ w i) (fun i ↦ hv i) hli n (hnweight n hn)
  · exact HomogeneousDenominator.finrank_le_of_component f hscalar
      (fun i : s ↦ v i) (fun i : s ↦ w i) (fun i ↦ hv i) hinj q hclear m hm n
      (fun i ↦ (hnweight n hn i).trans (Nat.le_add_right n m))

end PaperP1.FiniteGradedModuleSandwich
