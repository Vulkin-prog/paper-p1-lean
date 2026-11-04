module

public import PaperP1.Model.RawWordObservation
public import PaperP1.Model.RawTwoWindowHosts
public import PaperP1.Affine.IndependentRows

/-! # Failure of raw-word independence produces an actual parity relation

The cylinder cutoff contains every positive observed integer. Evaluating
the finite row relation on each prime basis vector then recovers the full
factorization-parity relation, including coordinates above the cutoff.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RawValueIndependence

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateValueSystem

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem surjective_of_injective_relations {M : ℕ} (v : ι → ℕ)
    (hinj : Function.Injective (PaperP1.Affine.relationMap (valueSystem M v))) :
    Function.Surjective (valueSystem M v) := by
  intro b
  have hm := PaperP1.Affine.uniformSolutionMass_of_injective_relationMap (valueSystem M v) hinj b
  have hp : 0 < PaperP1.Affine.uniformSolutionMass (valueSystem M v) b := by
    rw [hm]
    exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card (ι → F₂))
  exact (PaperP1.Affine.uniformSolutionMass_pos_iff (valueSystem M v) b).mp hp

omit [DecidableEq ι] in
theorem relation_of_zero_functional {M : ℕ} (v : ι → ℕ)
    (hpos : ∀ i, 0 < v i) (hcut : ∀ i, v i ≤ M) (u : ι → F₂)
    (hu : PaperP1.Affine.relationMap (valueSystem M v) u = 0) :
    (∑ i, u i • parityVec (v i)) = 0 := by
  ext p
  by_cases hp : p.Prime
  · by_cases hpM : p ≤ M
    · let q : PrimeUpTo M := ⟨⟨p, by omega⟩, hp⟩
      have hz := LinearMap.congr_fun hu (Pi.single q 1 : SampleSpace M)
      change dotProduct u (valueSystem M v (Pi.single q 1)) = 0 at hz
      simpa only [dotProduct, valueSystem_apply, valueBit_prime_basis,
        Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul,
        Finsupp.zero_apply] using hz
    · have hz : ∀ i, parityVec (v i) p = 0 := by
        intro i
        rw [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd, Nat.cast_zero]
        exact Nat.not_dvd_of_pos_of_lt (hpos i) ((hcut i).trans_lt (by omega))
      simp only [Finset.sum_apply', Finsupp.smul_apply, hz, smul_zero,
        sum_const_zero, Finsupp.zero_apply]
  · simp only [Finset.sum_apply', Finsupp.smul_apply, parityVec_apply,
      Nat.factorization_eq_zero_of_not_prime _ hp, Nat.cast_zero, smul_zero,
      sum_const_zero, Finsupp.zero_apply]

theorem non_surjective_relation {M : ℕ} (v : ι → ℕ)
    (hpos : ∀ i, 0 < v i) (hcut : ∀ i, v i ≤ M)
    (hn : ¬Function.Surjective (valueSystem M v)) :
    ∃ u : ι → F₂, u ≠ 0 ∧ (∑ i, u i • parityVec (v i)) = 0 := by
  classical
  by_contra h
  apply hn
  apply surjective_of_injective_relations
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro u hu
  have hrel := relation_of_zero_functional v hpos hcut u (LinearMap.mem_ker.mp hu)
  have hu0 : u = 0 := by
    by_contra hu0
    exact h ⟨u, hu0, hrel⟩
  simpa only [Submodule.mem_bot] using hu0

omit [Fintype ι] [DecidableEq ι] in
theorem joint_surjective_of_combined {κ : Type*} {M : ℕ} (v : ι → ℕ) (t : κ → ℕ)
    (h : Function.Surjective (valueSystem M (Sum.elim v t))) :
    Function.Surjective (PaperP1.RawWordObservation.joint M v t) := by
  intro b
  obtain ⟨ω, hω⟩ := h (Sum.elim b.1 b.2)
  refine ⟨ω, Prod.ext ?_ ?_⟩
  · funext i
    exact congrFun hω (Sum.inl i)
  · funext i
    exact congrFun hω (Sum.inr i)

theorem joint_non_surjective_related {M x y B : ℕ}
    (hx : ∀ i : Fin B, 0 < x - 1 + i.val) (hy : ∀ i : Fin B, 0 < y - 1 + i.val)
    (hxc : ∀ i : Fin B, x - 1 + i.val ≤ M) (hyc : ∀ i : Fin B, y - 1 + i.val ≤ M)
    (hn : ¬Function.Surjective (PaperP1.RawWordObservation.joint M
      (fun i : Fin B ↦ x - 1 + i.val) (fun i : Fin B ↦ y - 1 + i.val))) :
    PaperP1.RawTwoWindowHosts.Related x y B := by
  classical
  let v : Fin B ⊕ Fin B → ℕ := Sum.elim (fun i ↦ x - 1 + i.val) (fun i ↦ y - 1 + i.val)
  have hp : ∀ i, 0 < v i := by intro i; cases i with | inl i => exact hx i | inr i => exact hy i
  have hc : ∀ i, v i ≤ M := by intro i; cases i with | inl i => exact hxc i | inr i => exact hyc i
  have hs : ¬Function.Surjective (valueSystem M v) := fun h ↦
    hn (joint_surjective_of_combined _ _ h)
  obtain ⟨u, hu, hrel⟩ := non_surjective_relation v hp hc hs
  refine ⟨(fun i ↦ u (Sum.inl i)), (fun i ↦ u (Sum.inr i)), ?_, ?_⟩
  · by_contra hnz
    push Not at hnz
    apply hu
    funext i
    cases i with
    | inl i => exact congrFun hnz.1 i
    | inr i => exact congrFun hnz.2 i
  · simpa only [Fintype.sum_sum_type, v, Sum.elim_inl, Sum.elim_inr] using hrel

end PaperP1.RawValueIndependence
