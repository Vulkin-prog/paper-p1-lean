module

public import PaperP1.Combinatorics.ComponentSelection
public import PaperP1.Coding.LocalDefectBound

/-! # The finite small-prime cost of components missing one of three blocks -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ColoredPrimeConstraints

open Finset PaperP1.Arithmetic PaperP1.LocalDefectBound PaperP1.CoverGraphResolution
  PaperP1.ComponentSelection PaperP1.PinnedGraphResolution

variable {V : Type*} [Fintype V] [DecidableEq V]

local instance coloredPrimeConstraintTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def parityMap (data : V → ℕ → F₂) : (V → F₂) →ₗ[F₂] (ℕ → F₂) where
  toFun f p := ∑ v, f v * data v p
  map_add' f g := by ext p; simp only [Pi.add_apply, add_mul, sum_add_distrib]
  map_smul' a f := by ext p; simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_sum, RingHom.id_apply]

def blockMap (color : V → Fin 3) : (V → F₂) →ₗ[F₂] (Fin 3 → F₂) where
  toFun f b := ∑ v ∈ univ.filter (fun v ↦ color v = b), f v
  map_add' f g := by ext b; simp only [Pi.add_apply, sum_add_distrib]
  map_smul' a f := by ext b; simp only [Pi.smul_apply, ← smul_sum, RingHom.id_apply]

def PairwiseRigid (color : V → Fin 3) (data : V → ℕ → F₂) : Prop :=
  ∀ k : Fin 3, ∀ f : V → F₂, (∀ v, color v = k → f v = 0) →
    parityMap data f = 0 → blockMap color f = 0 → f = 0

abbrev LargePrime (H : ℕ) := {p : ℕ // p.Prime ∧ H < p}

def otherBlocks (k : Fin 3) : Finset (Fin 3) := univ.erase k

abbrev ConstraintTarget (H : ℕ) (k : Fin 3) :=
  (Fin (primeCount H) → F₂) × (otherBlocks k → F₂)

def smallConstraints (color : V → Fin 3) (data : V → ℕ → F₂) (H : ℕ) (k : Fin 3) :
    (V → F₂) →ₗ[F₂] ConstraintTarget H k where
  toFun f := (fun i ↦ parityMap data f (smallPrime H i), fun b ↦ blockMap color f b.val)
  map_add' f g := by apply Prod.ext <;> funext i <;> simp only [map_add, Pi.add_apply, Prod.fst_add, Prod.snd_add]
  map_smul' a f := by apply Prod.ext <;> funext i <;> simp only [map_smul, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]

theorem finrank_constraintTarget (H : ℕ) (k : Fin 3) :
    Module.finrank F₂ (ConstraintTarget H k) = primeCount H + 2 := by
  change Module.finrank F₂ ((Fin (primeCount H) → F₂) × (otherBlocks k → F₂)) = _
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin, Fintype.card_coe]
  simp only [otherBlocks, card_erase_of_mem (mem_univ _), card_univ]
  norm_num

theorem selection_kernel_trivial (color : V → Fin 3) (data : V → ℕ → F₂) (H : ℕ)
    (rows : LargePrime H → Finset V) (hrows : ∀ p, (rows p).card ≤ 3)
    (hrow : ∀ (p : LargePrime H) (f : V → F₂), parityMap data f p.val = ∑ v ∈ rows p, f v)
    (hnonprime : ∀ (p : ℕ), ¬p.Prime → ∀ v, data v p = 0) (hrigid : PairwiseRigid color data)
    {D : Finset V} (hD : IsCover rows D) (k : Fin 3) (Q : Finset (graph rows D).ConnectedComponent)
    (hfree : ∀ c ∈ Q, ¬ComponentPinned (graph rows D) (pins rows D) c)
    (hmissing : ∀ c ∈ Q, ∀ v ∈ c.supp, color v ≠ k) (f : Q → F₂)
    (hf : smallConstraints color data H k (selection (graph rows D) Q f) = 0) : f = 0 := by
  let g := selection (graph rows D) Q f
  have hsupport : ∀ v, color v = k → g v = 0 := selection_supported _ color k Q hmissing f
  have hgraph := selection_mem_zeroed_rows hrows hD Q hfree f
  have hparity : parityMap data g = 0 := by
    funext p
    change parityMap data g p = 0
    by_cases hp : p.Prime
    · by_cases hpH : p ≤ H
      · obtain ⟨i, hi⟩ := smallPrime_covers hp hpH
        have h := congrArg (fun z : ConstraintTarget H k ↦ z.1 i) hf
        change parityMap data g (smallPrime H i) = 0 at h
        simpa only [hi] using h
      · rw [hrow ⟨p, hp, Nat.lt_of_not_ge hpH⟩ g]
        exact hgraph.1 ⟨p, hp, Nat.lt_of_not_ge hpH⟩
    · change (∑ v, g v * data v p) = 0
      simp only [hnonprime p hp, mul_zero, sum_const_zero]
  have hblocks : blockMap color g = 0 := by
    funext b
    change blockMap color g b = 0
    by_cases hbk : b = k
    · subst b
      apply sum_eq_zero
      intro v hv
      exact hsupport v (mem_filter.mp hv).2
    · have hb : b ∈ otherBlocks k := mem_erase.mpr ⟨hbk, mem_univ _⟩
      have h := congrArg (fun z : ConstraintTarget H k ↦ z.2 ⟨b, hb⟩) hf
      exact h
  have hg : g = 0 := hrigid k g hsupport hparity hblocks
  apply (selection_injective (graph rows D) Q)
  simpa only [map_zero] using hg

theorem missing_components_card_bound (color : V → Fin 3) (data : V → ℕ → F₂) (H : ℕ)
    (rows : LargePrime H → Finset V) (hrows : ∀ p, (rows p).card ≤ 3)
    (hrow : ∀ (p : LargePrime H) (f : V → F₂), parityMap data f p.val = ∑ v ∈ rows p, f v)
    (hnonprime : ∀ (p : ℕ), ¬p.Prime → ∀ v, data v p = 0) (hrigid : PairwiseRigid color data)
    {D : Finset V} (hD : IsCover rows D) (k : Fin 3) (Q : Finset (graph rows D).ConnectedComponent)
    (hfree : ∀ c ∈ Q, ¬ComponentPinned (graph rows D) (pins rows D) c)
    (hmissing : ∀ c ∈ Q, ∀ v ∈ c.supp, color v ≠ k) : Q.card ≤ primeCount H + 2 := by
  classical
  let T := (smallConstraints color data H k).comp (selection (graph rows D) Q)
  have hT : Function.Injective T := by
    intro f g hfg
    apply sub_eq_zero.mp
    apply selection_kernel_trivial color data H rows hrows hrow hnonprime hrigid hD k Q hfree hmissing (f - g)
    change T (f - g) = 0
    rw [map_sub, hfg, sub_self]
  have hdim := LinearMap.finrank_le_finrank_of_injective hT
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, finrank_constraintTarget] at hdim
  exact hdim

end PaperP1.ColoredPrimeConstraints
