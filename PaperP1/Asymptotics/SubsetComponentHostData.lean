module

public import PaperP1.Asymptotics.SubsetComponentSystems

/-! # Actual two-subset small and singleton-target components supply counted root-system data -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SubsetComponentHostData

open Finset PaperP1.Arithmetic PaperP1.AsymmetricEnvelopeGraph PaperP1.AsymmetricComponentOffsets
  PaperP1.LargePrimeGraph PaperP1.PinnedGraphResolution PaperP1.TwoBlockComponentSquares
  PaperP1.SplitRadicalPointHeight

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def nontrivial (x y H R : ℕ) (U V : Finset ℕ) :
    Finset (largePrimeGraph (start x R) (start y R) H).ConnectedComponent :=
  (unpinnedComponents (largePrimeGraph (start x R) (start y R) H) (SubsetEnvelopeGraph.pins x y H R U V)).filter
    fun c ↦ 2 ≤ Fintype.card c.supp

def small (x y H R : ℕ) (U V : Finset ℕ) (K : ℕ) :
    Finset (largePrimeGraph (start x R) (start y R) H).ConnectedComponent :=
  MediumPrimeColumns.smallComponents (start x R) (start y R) H (nontrivial x y H R U V) K

def typed (x y H R : ℕ) (U V : Finset ℕ) (a : ℕ) :
    Finset (largePrimeGraph (start x R) (start y R) H).ConnectedComponent :=
  (nontrivial x y H R U V).filter fun c ↦
    (left x y H R c).card = a ∧ (right x y H R c).card = 1

theorem mem_nontrivial (x y H R : ℕ) (U V : Finset ℕ)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent) :
    c ∈ nontrivial x y H R U V ↔
      ¬ComponentPinned _ (SubsetEnvelopeGraph.pins x y H R U V) c ∧ 2 ≤ Fintype.card c.supp := by
  simp only [nontrivial, mem_filter, mem_unpinnedComponents]

theorem mem_small (x y H R : ℕ) (U V : Finset ℕ) (K : ℕ)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent) :
    c ∈ small x y H R U V K ↔
      ¬ComponentPinned _ (SubsetEnvelopeGraph.pins x y H R U V) c ∧ 2 ≤ Fintype.card c.supp ∧
        (vertices (start x R) (start y R) H c).card ≤ K := by
  simp only [small, MediumPrimeColumns.smallComponents, mem_filter, mem_nontrivial, and_assoc, vertices]

theorem mem_typed (x y H R : ℕ) (U V : Finset ℕ) (a : ℕ)
    (c : (largePrimeGraph (start x R) (start y R) H).ConnectedComponent) :
    c ∈ typed x y H R U V a ↔
      ¬ComponentPinned _ (SubsetEnvelopeGraph.pins x y H R U V) c ∧ 2 ≤ Fintype.card c.supp ∧
        (left x y H R c).card = a ∧ (right x y H R c).card = 1 := by
  simp only [typed, mem_filter, mem_nontrivial, and_assoc]

theorem exists_general {x y H R : ℕ} (hx : R < x) (hy : R < y)
    (hR : 1 ≤ R) (U V : Finset ℕ)
    (hold : ∀ n ∈ U, |(n : ℤ) - x| ≤ (R : ℤ))
    (hnew : ∀ n ∈ V, |(n : ℤ) - y| ≤ (R : ℤ)) (k K : ℕ)
    (hcount : k ≤ (small x y H R U V K).card) :
    ∃ q ∈ GeneralSplitRadicalPatternPool.pool k (R - 1) (10 * (H + 1)) K,
      SmoothGeneralNonalignedHostCount.Valid K q ∧ ∃ w : Fin k → ℤ,
      ∀ i, w i ^ 2 = GeneralSplitRadicalPatternPool.coefficient q i *
        integerProduct (q.1.1 i) (x : ℤ) * integerProduct (q.1.2 i) (y : ℤ) := by
  classical
  let Cset := small x y H R U V K
  let e : Cset ≃ Fin Cset.card := Fintype.equivFinOfCardEq (Fintype.card_coe Cset)
  let f : Fin k → Cset := fun i ↦ e.symm (Fin.castLE hcount i)
  have hf : Function.Injective f := e.symm.injective.comp (Fin.castLE_injective hcount)
  let c : Fin k → (largePrimeGraph (start x R) (start y R) H).ConnectedComponent := fun i ↦ (f i).val
  have hc : Function.Injective c := fun _ _ he ↦ hf (Subtype.ext he)
  have hd (i) := (mem_small x y H R U V K (c i)).mp (f i).property
  exact SubsetComponentSystems.exists_general hx hy hR U V hold hnew k K c hc
    (fun i ↦ (hd i).1) (fun i ↦ (hd i).2.1) (fun i ↦ (hd i).2.2)

theorem exists_linear {x y H R : ℕ} (hx : R < x) (hy : R < y)
    (hR : 1 ≤ R) (U V : Finset ℕ)
    (hold : ∀ n ∈ U, |(n : ℤ) - x| ≤ (R : ℤ))
    (hnew : ∀ n ∈ V, |(n : ℤ) - y| ≤ (R : ℤ)) (k a K : ℕ) (hK : a + 1 ≤ K)
    (hcount : k ≤ (typed x y H R U V a).card) :
    ∃ q ∈ SplitRadicalPatternPool.pool k (R - 1) (10 * (H + 1)) K,
      SmoothDegreeOneHostCount.Valid a K q ∧ ∃ w : Fin k → ℤ,
      ∀ i, w i ^ 2 = SplitRadicalPatternPool.coefficient q i *
        integerProduct (q.1.1 i) (x : ℤ) * ((y : ℤ) + q.1.2 i) := by
  classical
  let Cset := typed x y H R U V a
  let e : Cset ≃ Fin Cset.card := Fintype.equivFinOfCardEq (Fintype.card_coe Cset)
  let f : Fin k → Cset := fun i ↦ e.symm (Fin.castLE hcount i)
  have hf : Function.Injective f := e.symm.injective.comp (Fin.castLE_injective hcount)
  let c : Fin k → (largePrimeGraph (start x R) (start y R) H).ConnectedComponent := fun i ↦ (f i).val
  have hc : Function.Injective c := fun _ _ he ↦ hf (Subtype.ext he)
  have hd (i) := (mem_typed x y H R U V a (c i)).mp (f i).property
  exact SubsetComponentSystems.exists_linear hx hy hR U V hold hnew k a K c hc
    (fun i ↦ (hd i).1) (fun i ↦ (hd i).2.2.1) (fun i ↦ (hd i).2.2.2) hK

end PaperP1.SubsetComponentHostData
