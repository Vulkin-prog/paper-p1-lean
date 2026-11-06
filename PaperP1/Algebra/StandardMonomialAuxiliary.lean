module

public import PaperP1.Algebra.StandardMonomialFamily
public import PaperP1.Algebra.IntegralEvaluationAnnihilator

/-! # Singular actual standard-monomial evaluation minors construct an independent auxiliary equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.StandardMonomialAuxiliary

open MvPolynomial Finset

variable {σ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_of_minors_zero (o : MonomialOrder σ) (q : MvPolynomial σ ℚ) (hq : q ≠ 0)
    (e : ℕ) (m : ι → σ →₀ ℕ) (hm : Function.Injective m) (hdegree : ∀ i, (m i).degree = e)
    (hstandard : ∀ i, ¬ o.degree q ≤ m i) (U : Finset (σ → ℤ))
    (hdet : ∀ f : ι → U, Function.Injective f →
      Matrix.det (fun i j ↦ (m j).prod (fun k r ↦ (f i).val k ^ r)) = 0) :
    ∃ G : MvPolynomial σ ℤ, G.IsHomogeneous e ∧ ¬ q ∣ map (Int.castRingHom ℚ) G ∧
      ∀ v ∈ U, eval v G = 0 := by
  classical
  let A : U → ι → ℤ := fun v j ↦ (m j).prod (fun k r ↦ v.val k ^ r)
  obtain ⟨w, hw, hzero⟩ := IntegralEvaluationAnnihilator.coefficients A hdet
  have hwQ : (fun i ↦ (w i : ℚ)) ≠ 0 := by
    intro hz
    apply hw
    funext i
    change w i = 0
    have hi : (w i : ℚ) = 0 := congrFun hz i
    exact_mod_cast hi
  refine ⟨StandardMonomialFamily.polynomial m w,
    StandardMonomialFamily.homogeneous m e hdegree w, ?_, ?_⟩
  · rw [StandardMonomialFamily.map_coefficients]
    exact StandardMonomialFamily.not_dvd o q hq m hm hstandard (fun i ↦ (w i : ℚ)) hwQ
  · intro v hv
    rw [StandardMonomialFamily.evaluation]
    exact hzero ⟨v, hv⟩

end PaperP1.StandardMonomialAuxiliary
