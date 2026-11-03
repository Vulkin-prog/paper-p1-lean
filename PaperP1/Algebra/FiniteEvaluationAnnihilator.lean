module

public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Data.Fintype.EquivFin

/-! # A common nonzero coefficient vector from vanishing maximal evaluation minors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteEvaluationAnnihilator

open Finset Matrix

variable {K : Type*} [Field K] {ι κ : Type*} [Fintype κ] [DecidableEq κ]

theorem span_ne_top (rows : ι → κ → K)
    (hdet : ∀ f : κ → ι, Function.Injective f → Matrix.det (fun i j ↦ rows (f i) j) = 0) :
    Submodule.span K (Set.range rows) ≠ ⊤ := by
  classical
  intro htop
  have hdim : Module.finrank K (Submodule.span K (Set.range rows)) = Fintype.card κ := by
    rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card]
  have hex := Submodule.exists_fun_fin_finrank_span_eq K (Set.range rows)
  rw [hdim] at hex
  obtain ⟨b, hb, _hspan, hli⟩ := hex
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  choose f hf using fun i : κ ↦ hb (e i)
  let A : Matrix κ κ K := fun i j ↦ rows (f i) j
  have hrow : A.row = b ∘ e := by funext i; exact hf i
  have hliA : LinearIndependent K A.row := by rw [hrow]; exact hli.comp e e.injective
  have hfinj : Function.Injective f := by
    intro i j hij
    apply hliA.injective
    change rows (f i) = rows (f j)
    rw [hij]
  exact (nonsingular_iff_det_ne_zero.mp (Nonsingular.of_linearIndependent_row hliA)) (hdet f hfinj)

theorem coefficients (rows : ι → κ → K)
    (hdet : ∀ f : κ → ι, Function.Injective f → Matrix.det (fun i j ↦ rows (f i) j) = 0) :
    ∃ w : κ → K, w ≠ 0 ∧ ∀ i, ∑ j, rows i j * w j = 0 := by
  classical
  let W := Submodule.span K (Set.range rows)
  have hproper : W ≠ ⊤ := span_ne_top rows hdet
  have hdual : W.dualAnnihilator ≠ ⊥ := by
    intro h
    exact hproper (Submodule.dualAnnihilator_eq_bot_iff.mp h)
  obtain ⟨φ, hφ, hφzero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hdual
  let w : κ → K := fun j ↦ φ (Pi.single j 1)
  have hformula (v : κ → K) : φ v = ∑ j, v j * w j := by
    have hv : v = ∑ j, v j • Pi.single j (1 : K) := by
      funext k
      simp [Pi.single_apply]
    conv_lhs => rw [hv, map_sum]
    simp only [map_smul, smul_eq_mul, w]
  refine ⟨w, ?_, ?_⟩
  · intro hw
    apply hφzero
    apply LinearMap.ext
    intro v
    rw [hformula, hw]
    simp
  · intro i
    rw [← hformula]
    exact (Submodule.mem_dualAnnihilator φ).mp hφ _ (Submodule.subset_span (Set.mem_range_self i))

end PaperP1.FiniteEvaluationAnnihilator
