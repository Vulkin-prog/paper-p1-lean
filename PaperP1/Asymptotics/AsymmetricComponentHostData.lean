module

public import PaperP1.Asymptotics.AsymmetricComponentSystems

/-! # Actual small and singleton-target components supply counted root-system data -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AsymmetricComponentHostData

open Finset PaperP1.Arithmetic PaperP1.AsymmetricEnvelopeGraph PaperP1.AsymmetricComponentOffsets
  PaperP1.LargePrimeGraph PaperP1.PinnedGraphResolution PaperP1.TwoBlockComponentSquares
  PaperP1.SplitRadicalPointHeight

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def nontrivial (x y L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ) :
    Finset (largePrimeGraph (start x R) (start y R) H).ConnectedComponent :=
  (unpinnedComponents (largePrimeGraph (start x R) (start y R) H) (pins x y L H R hnew hamb old)).filter
    fun c ↦ 2 ≤ Fintype.card c.supp

def small (x y L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ) (K : ℕ) :
    Finset (largePrimeGraph (start x R) (start y R) H).ConnectedComponent :=
  MediumPrimeColumns.smallComponents (start x R) (start y R) H (nontrivial x y L H R hnew hamb old) K

def typed (x y L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ) (a : ℕ) :
    Finset (largePrimeGraph (start x R) (start y R) H).ConnectedComponent :=
  (nontrivial x y L H R hnew hamb old).filter fun c ↦
    (left x y H R c).card = a ∧ (right x y H R c).card = 1

theorem mem_nontrivial (x y L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent) :
    c ∈ nontrivial x y L H R hnew hamb old ↔
      ¬ComponentPinned _ (pins x y L H R hnew hamb old) c ∧ 2 ≤ Fintype.card c.supp := by
  simp only [nontrivial, mem_filter, mem_unpinnedComponents]

theorem mem_small (x y L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ) (K : ℕ)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent) :
    c ∈ small x y L H R hnew hamb old K ↔
      ¬ComponentPinned _ (pins x y L H R hnew hamb old) c ∧ 2 ≤ Fintype.card c.supp ∧
        (vertices (start x R) (start y R) H c).card ≤ K := by
  simp only [small, MediumPrimeColumns.smallComponents, mem_filter, mem_nontrivial, and_assoc, vertices]

theorem mem_typed (x y L H R : ℕ) (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ) (a : ℕ)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent) :
    c ∈ typed x y L H R hnew hamb old a ↔
      ¬ComponentPinned _ (pins x y L H R hnew hamb old) c ∧ 2 ≤ Fintype.card c.supp ∧
        (left x y H R c).card = a ∧ (right x y H R c).card = 1 := by
  simp only [typed, mem_filter, mem_nontrivial, and_assoc]

theorem exists_general {x y L H R : ℕ} (hx : R < x) (hy : R < y)
    (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ)
    (hold : ∀ n ∈ old, |(n : ℤ) - x| ≤ (R : ℤ)) (k K : ℕ)
    (hcount : k ≤ (small x y L H R hnew hamb old K).card) :
    ∃ q ∈ GeneralSplitRadicalPatternPool.pool k (R - 1) (10 * (H + 1)) K,
      SmoothGeneralNonalignedHostCount.Valid K q ∧ ∃ w : Fin k → ℤ,
      ∀ i, w i ^ 2 = GeneralSplitRadicalPatternPool.coefficient q i *
        integerProduct (q.1.1 i) (x : ℤ) * integerProduct (q.1.2 i) (y : ℤ) := by
  classical
  let U := small x y L H R hnew hamb old K
  let e : U ≃ Fin U.card := Fintype.equivFinOfCardEq (Fintype.card_coe U)
  let f : Fin k → U := fun i ↦ e.symm (Fin.castLE hcount i)
  have hf : Function.Injective f := e.symm.injective.comp (Fin.castLE_injective hcount)
  let c : Fin k → (largePrimeGraph (start x R) (start y R) H).ConnectedComponent := fun i ↦ (f i).val
  have hc : Function.Injective c := fun _ _ he ↦ hf (Subtype.ext he)
  have hd (i) := (mem_small x y L H R hnew hamb old K (c i)).mp (f i).property
  exact AsymmetricComponentSystems.exists_general hx hy hnew hamb old hold k K c hc
    (fun i ↦ (hd i).1) (fun i ↦ (hd i).2.1) (fun i ↦ (hd i).2.2)

theorem exists_linear {x y L H R : ℕ} (hx : R < x) (hy : R < y)
    (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ)
    (hold : ∀ n ∈ old, |(n : ℤ) - x| ≤ (R : ℤ)) (k a K : ℕ) (hK : a + 1 ≤ K)
    (hcount : k ≤ (typed x y L H R hnew hamb old a).card) :
    ∃ q ∈ SplitRadicalPatternPool.pool k (R - 1) (10 * (H + 1)) K,
      SmoothDegreeOneHostCount.Valid a K q ∧ ∃ w : Fin k → ℤ,
      ∀ i, w i ^ 2 = SplitRadicalPatternPool.coefficient q i *
        integerProduct (q.1.1 i) (x : ℤ) * ((y : ℤ) + q.1.2 i) := by
  classical
  let U := typed x y L H R hnew hamb old a
  let e : U ≃ Fin U.card := Fintype.equivFinOfCardEq (Fintype.card_coe U)
  let f : Fin k → U := fun i ↦ e.symm (Fin.castLE hcount i)
  have hf : Function.Injective f := e.symm.injective.comp (Fin.castLE_injective hcount)
  let c : Fin k → (largePrimeGraph (start x R) (start y R) H).ConnectedComponent := fun i ↦ (f i).val
  have hc : Function.Injective c := fun _ _ he ↦ hf (Subtype.ext he)
  have hd (i) := (mem_typed x y L H R hnew hamb old a (c i)).mp (f i).property
  exact AsymmetricComponentSystems.exists_linear hx hy hnew hamb old hold k a K c hc
    (fun i ↦ (hd i).1) (fun i ↦ (hd i).2.2.1) (fun i ↦ (hd i).2.2.2) hK

end PaperP1.AsymmetricComponentHostData
