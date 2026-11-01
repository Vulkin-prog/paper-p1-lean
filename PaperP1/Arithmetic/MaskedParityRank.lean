module

public import PaperP1.Algebra.FiniteSetRelativeRank
public import PaperP1.Algebra.EvenImageMap
public import PaperP1.Arithmetic.FiniteResidualRank

/-! # Relative rank modulo old true values after deleting any finite set of prime rows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MaskedParityRank

open Finset PaperP1.Arithmetic PaperP1.PrimeRowComponents

local instance maskedParityPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def project (P : Finset ℕ) : (ℕ →₀ F₂) →ₗ[F₂] (ℕ → F₂) where
  toFun f p := if p ∈ P then 0 else f p
  map_add' f g := by ext p; by_cases hp : p ∈ P <;> simp [hp]
  map_smul' a f := by ext p; by_cases hp : p ∈ P <;> simp [hp]

def data (P : Finset ℕ) (n : ℕ) : ℕ → F₂ := project P (parityVec n)

def relativeKernel (P S T : Finset ℕ) :
    Submodule F₂ (LinearMap.ker (EvenSupportRank.sumMap F₂ T)) :=
  FiniteSetRelativeRank.relativeKernel (K := F₂) (data P) S T

theorem fullMap_apply (P S : Finset ℕ) (w : S → F₂) (p : ℕ) :
    FiniteSetValueSpan.fullMap (K := F₂) (data P) S w p =
      if p ∈ P then 0 else ∑ n : S, w n * parityVec n.val p := by
  by_cases hp : p ∈ P <;>
    simp [FiniteSetValueSpan.fullMap, EvenImage.combination_apply, FiniteSetValueSpan.data,
      data, project, Finset.sum_apply, smul_eq_mul, hp]

theorem kernel_eq_rows (P S : Finset ℕ) :
    FiniteSetValueSpan.valueKernel (K := F₂) (data P) S = CoverGraphResolution.rowSolutions (rows S P) := by
  ext w
  constructor
  · intro hw p
    by_cases hp : p ∈ P
    · simp only [rows, ite_eq_left hp, sum_empty]
    · rw [sum_row p hp]
      have h := congrFun (LinearMap.mem_ker.mp hw) p
      simpa only [fullMap_apply, ite_eq_right hp, Pi.zero_apply] using h
  · intro hw
    apply LinearMap.mem_ker.mpr
    funext p
    change FiniteSetValueSpan.fullMap (K := F₂) (data P) S w p = 0
    rw [fullMap_apply]
    by_cases hp : p ∈ P
    · rw [ite_eq_left hp]
    · rw [ite_eq_right hp]
      have h := hw p
      rwa [sum_row p hp] at h

theorem evenSpace_eq_map (P S : Finset ℕ) :
    FiniteSetValueSpan.evenSpace (K := F₂) (data P) S = (FiniteEvenSquareClasses.space S).map (project P) := by
  change EvenImage.image (K := F₂) (fun n : S ↦ project P (parityVec n.val)) =
    (EvenImage.image (K := F₂) (FiniteEvenSquareClasses.data S)).map (project P)
  exact EvenImageMap.image_map (project P) (FiniteEvenSquareClasses.data S)

theorem matches_add_residual (P S T : Finset ℕ) :
    Module.finrank F₂ (relativeKernel P S T) ≤ (S ∩ T).card +
      Module.finrank F₂ (CoverGraphResolution.rowSolutions (rows (S ∪ T) P)) := by
  have h := FiniteSetRelativeRank.matches_add_residual (K := F₂) (data P) S T
  rw [kernel_eq_rows] at h
  exact h

theorem finite_loss_bound {P S T : Finset ℕ} {K U R t : ℕ}
    (hrows : ∀ p, (rows (S ∪ T) P p).card ≤ 2)
    (hlower : ∀ n ∈ S ∪ T, U ≤ n) (hupper : ∀ n ∈ S ∪ T, n ≤ U + R)
    (hR : 1 ≤ R) (hU : 2 * R ≤ U) (hgrowth : (64 * R) ^ (2 * (K * t)) < U) (ht : 1 ≤ t) :
    Module.finrank F₂ (relativeKernel P S T) < (S ∩ T).card +
      max (P.card + 1) (2 * t * 2 ^ ((P.card + 1) / t + 1)) + (S ∪ T).card / (K + 1) := by
  have hrelative := matches_add_residual P S T
  have hresidual := FiniteResidualRank.finite_row_rank_bound hrows hlower hupper hR hU hgrowth ht
  omega

end PaperP1.MaskedParityRank
