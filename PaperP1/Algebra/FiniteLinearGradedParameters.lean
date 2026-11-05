module

public import PaperP1.Algebra.FiniteGradedSupport
public import PaperP1.Algebra.GradedModulePieceMap
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.FiniteType

/-! # Actual degree-one parameters with a finite-dimensional zero fibre give a finite algebra -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteLinearGradedParameters

open DirectSum MvPolynomial

theorem finite_adjoin_of_eventual_span {F A ι : Type*} [Field F] [CommRing A] [Algebra F A] [Fintype ι]
    (H : ℕ → Submodule F A) [GradedAlgebra H] [∀ n, Module.Finite F (H n)]
    (g : ι → A) (hg : ∀ i, g i ∈ H 1) (N : ℕ) (hN : 0 < N)
    (hcut : ∀ n : ℕ, N ≤ n → H n ≤ (Ideal.span (Set.range g)).restrictScalars F) :
    Module.Finite (Algebra.adjoin F (Set.range g)) A := by
  classical
  let R := Algebra.adjoin F (Set.range g)
  let W : Submodule F A := ⨆ j : Fin N, H j.val
  have hfg : W.FG := Submodule.fg_iSup _ (fun j ↦ Module.Finite.iff_fg.mp inferInstance)
  obtain ⟨S, hS⟩ := hfg
  let U := Submodule.span R (S : Set A)
  have hWU : W ≤ U.restrictScalars F := by
    rw [← hS]
    exact Submodule.span_le.mpr (fun _ hs ↦ Submodule.subset_span hs)
  have hpieces (n : ℕ) : H n ≤ U.restrictScalars F := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      by_cases hn : n < N
      · exact hWU ((le_iSup (fun j : Fin N ↦ H j.val) ⟨n, hn⟩) hx)
      · have hnN : N ≤ n := Nat.le_of_not_gt hn
        have hn1 : 1 ≤ n := hN.trans_le hnN
        obtain ⟨a, ha⟩ := (Ideal.mem_span_range_iff_exists_fun).mp (hcut n hnN hx)
        have he : ∑ i, (decompose H (a i) (n - 1) : A) * g i = x := by
          simpa only [GradedRingHom.id_apply] using
            GradedModulePieceMap.homogeneous_representation (GradedRingHom.id H) g (fun _ ↦ 1) hg
              n (fun _ ↦ hn1) hx a ha
        rw [← he]
        apply U.sum_mem
        intro i _hi
        have hc : (decompose H (a i) (n - 1) : A) ∈ U :=
          ih (n - 1) (by omega) (decompose H (a i) (n - 1)).property
        let gi : R := ⟨g i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
        have hm := U.smul_mem gi hc
        change g i * (decompose H (a i) (n - 1) : A) ∈ U at hm
        simpa only [mul_comm] using hm
  have htop : U = ⊤ := by
    apply top_unique
    intro x _hx
    rw [← sum_support_decompose H x]
    exact U.sum_mem (fun n _hn ↦ hpieces n (decompose H x n).property)
  exact ⟨⟨S, htop⟩⟩

theorem finite_adjoin_of_finite_quotient {F A ι : Type*} [Field F] [CommRing A] [Algebra F A] [Fintype ι]
    (H : ℕ → Submodule F A) [GradedAlgebra H] [∀ n, Module.Finite F (H n)]
    (g : ι → A) (hg : ∀ i, g i ∈ H 1)
    [Module.Finite F (A ⧸ Ideal.span (Set.range g))] :
    Module.Finite (Algebra.adjoin F (Set.range g)) A := by
  have hJ : (Ideal.span (Set.range g)).IsHomogeneous H :=
    Ideal.homogeneous_span H _ (by rintro _ ⟨i, rfl⟩; exact ⟨1, hg i⟩)
  obtain ⟨N, hN, hcut⟩ := FiniteGradedSupport.eventually_le_ideal H _ hJ
  exact finite_adjoin_of_eventual_span H g hg N hN hcut

theorem finite_evaluation_of_adjoin {F A ι : Type*} [Field F] [CommRing A] [Algebra F A]
    (g : ι → A) (hfinite : Module.Finite (Algebra.adjoin F (Set.range g)) A) :
    (aeval (R := F) g).Finite := by
  have hrange : Module.Finite (aeval (R := F) g).range A := by
    rw [MvPolynomial.aeval_range]
    exact hfinite
  have hval : (Subalgebra.val (aeval (R := F) g).range).Finite := by
    change (algebraMap (aeval (R := F) g).range A).Finite
    exact RingHom.finite_algebraMap.mpr hrange
  rw [← AlgHom.val_comp_rangeRestrict (φ := aeval (R := F) g)]
  exact AlgHom.Finite.comp hval (AlgHom.Finite.of_surjective _ (AlgHom.rangeRestrict_surjective _))

theorem finite_evaluation_of_eventual_span {F A ι : Type*} [Field F] [CommRing A] [Algebra F A] [Fintype ι]
    (H : ℕ → Submodule F A) [GradedAlgebra H] [∀ n, Module.Finite F (H n)]
    (g : ι → A) (hg : ∀ i, g i ∈ H 1) (N : ℕ) (hN : 0 < N)
    (hcut : ∀ n : ℕ, N ≤ n → H n ≤ (Ideal.span (Set.range g)).restrictScalars F) :
    (aeval (R := F) g).Finite :=
  finite_evaluation_of_adjoin g (finite_adjoin_of_eventual_span H g hg N hN hcut)

end PaperP1.FiniteLinearGradedParameters
