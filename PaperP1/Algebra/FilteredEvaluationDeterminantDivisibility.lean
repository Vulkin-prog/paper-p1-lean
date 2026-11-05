module

public import PaperP1.Algebra.WeightedEvaluationDeterminant
public import Mathlib.Algebra.Order.Group.Int.Sum
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span

/-! # Triangular-power divisibility of a filtered evaluation determinant

Distinct selected monomial degrees contribute at least 0+1+...+(k-1).
This finite algebraic lemma requires no prime or analytic convergence assumption.
Its application to actual smooth residue classes is a separate task.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FilteredEvaluationDeterminantDivisibility

open Finset PaperP1.WeightedEvaluationDeterminant

theorem distinct_degree_budget {k M : ℕ} (f : Fin k → Fin M) (hf : Function.Injective f) :
    (∑ i ∈ Finset.range k, i) ≤ ∑ i, (f i).val := by
  classical
  let g : Fin k → ℤ := fun i ↦ (f i).val
  have hg : Function.Injective g := by
    intro i j he
    apply hf
    apply Fin.ext
    change ((f i).val : ℤ) = ((f j).val : ℤ) at he
    exact Int.ofNat_injective he
  let S := (univ : Finset (Fin k)).image g
  have hcard : S.card = k := by
    dsimp only [S]
    rw [Finset.card_image_of_injective _ hg]
    simp
  have hsum : (∑ z ∈ S, z) = ∑ i, g i := by
    dsimp only [S]
    rw [Finset.sum_image (fun i _hi j _hj he ↦ hg he)]
  have hnonneg : ∀ z ∈ S, (0 : ℤ) ≤ z := by
    intro z hz
    obtain ⟨i, _hi, rfl⟩ := mem_image.mp hz
    exact Nat.cast_nonneg _
  have hs := Finset.sum_range_le_sum hnonneg
  rw [hcard, hsum] at hs
  simp only [zero_add] at hs
  dsimp only [g] at hs
  have hs' : ((∑ i ∈ Finset.range k, i : ℕ) : ℤ) ≤ ((∑ i, (f i).val : ℕ) : ℤ) := by
    simpa only [Nat.cast_sum] using hs
  exact_mod_cast hs'

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

theorem row_power_dvd (p : R) (M : Matrix ι ι R) (w : ι → ℕ)
    (hM : ∀ i j, p ^ w i ∣ M i j) : p ^ (∑ i, w i) ∣ M.det := by
  classical
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro σ _hσ
  have hp : (∏ i, p ^ w (σ i)) ∣ ∏ i, M (σ i) i :=
    Finset.prod_dvd_prod_of_dvd (fun i ↦ p ^ w (σ i)) (fun i ↦ M (σ i) i)
      (fun i _hi ↦ hM (σ i) i)
  rw [Finset.prod_pow_eq_pow_sum, Equiv.sum_comp σ w] at hp
  exact dvd_mul_of_dvd_right hp _

theorem evaluation_dvd (p : R) (k M : ℕ) (C : Fin k → Fin M → R) (V : Fin M → Fin k → R)
    (hV : ∀ r j, p ^ r.val ∣ V r j) :
    p ^ (∑ i ∈ Finset.range k, i) ∣ (evaluationMatrix C V).det := by
  classical
  rw [determinant_injective_expansion]
  apply Finset.dvd_sum
  intro f hf
  have hi : Function.Injective f := (mem_filter.mp hf).2
  have hd : p ^ (∑ i, (f i).val) ∣ (selectedMatrix V f).det :=
    row_power_dvd p (selectedMatrix V f) (fun i ↦ (f i).val) (fun i j ↦ hV (f i) j)
  have hp := pow_dvd_pow p (distinct_degree_budget f hi)
  exact dvd_mul_of_dvd_right (hp.trans hd) _

theorem evaluation_triangular_dvd (p : R) (k M : ℕ)
    (C : Fin k → Fin M → R) (V : Fin M → Fin k → R)
    (hV : ∀ r j, p ^ r.val ∣ V r j) :
    p ^ (k * (k - 1) / 2) ∣ (evaluationMatrix C V).det := by
  simpa only [Finset.sum_range_id] using evaluation_dvd p k M C V hV

theorem determinant_congruence_dvd (d : R) (M N : Matrix ι ι R)
    (hMN : ∀ i j, d ∣ M i j - N i j) : d ∣ M.det - N.det := by
  let I : Ideal R := Ideal.span {d}
  let φ := Ideal.Quotient.mk I
  have he : φ.mapMatrix M = φ.mapMatrix N := by
    ext i j
    change Ideal.Quotient.mk I (M i j) = Ideal.Quotient.mk I (N i j)
    apply Ideal.Quotient.eq.mpr
    exact Ideal.mem_span_singleton.mpr (hMN i j)
  have hdet : φ M.det = φ N.det := by rw [φ.map_det, φ.map_det, he]
  have hz : φ (M.det - N.det) = 0 := by rw [map_sub, hdet, sub_self]
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)

theorem evaluation_congruent_dvd (p : R) (k M : ℕ)
    (C : Fin k → Fin M → R) (V : Fin M → Fin k → R) (A : Matrix (Fin k) (Fin k) R)
    (hV : ∀ r j, p ^ r.val ∣ V r j)
    (hA : ∀ i j, p ^ (k * (k - 1) / 2) ∣ A i j - evaluationMatrix C V i j) :
    p ^ (k * (k - 1) / 2) ∣ A.det := by
  have hdiff := determinant_congruence_dvd (p ^ (k * (k - 1) / 2)) A (evaluationMatrix C V) hA
  have hadd := dvd_add hdiff (evaluation_triangular_dvd p k M C V hV)
  simpa only [sub_add_cancel] using hadd

end PaperP1.FilteredEvaluationDeterminantDivisibility
