module

public import PaperP1.Arithmetic.AsymmetricComponentOffsets
public import PaperP1.Asymptotics.EnlargedSmoothGeneralHostCount
public import PaperP1.Asymptotics.EnlargedSmoothDegreeOneHostCount

/-! # Actual asymmetric free components construct the complete enumerated root systems -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AsymmetricComponentSystems

open Finset PaperP1.Arithmetic PaperP1.AsymmetricEnvelopeGraph PaperP1.AsymmetricComponentOffsets
  PaperP1.LargePrimeGraph PaperP1.PinnedGraphResolution PaperP1.TwoBlockComponentSquares
  PaperP1.DefectivePredicate PaperP1.SplitRadicalPointHeight

local instance (P : Prop) : Decidable P := Classical.propDecidable P

open PaperP1.GeneralSplitRadicalPatternPool in
theorem exists_general {x y L H R : ℕ} (hx : R < x) (hy : R < y)
    (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ)
    (hold : ∀ n ∈ old, |(n : ℤ) - x| ≤ (R : ℤ)) (k K : ℕ)
    (c : Fin k → (largePrimeGraph (start x R) (start y R) H).ConnectedComponent) (hcinj : Function.Injective c)
    (hfree : ∀ i, ¬ComponentPinned _ (pins x y L H R hnew hamb old) (c i))
    (hnon : ∀ i, 2 ≤ Fintype.card (c i).supp)
    (hK : ∀ i, (vertices (start x R) (start y R) H (c i)).card ≤ K) :
    ∃ q ∈ pool k (R - 1) (10 * (H + 1)) K, SmoothGeneralNonalignedHostCount.Valid K q ∧
      ∃ w : Fin k → ℤ, ∀ i, w i ^ 2 = coefficient q i *
        integerProduct (q.1.1 i) (x : ℤ) * integerProduct (q.1.2 i) (y : ℤ) := by
  classical
  have hW : R - 1 + 1 = R := by omega
  let q : Pattern k := ((fun i ↦ left x y H R (c i), fun i ↦ right x y H R (c i)),
    fun i ↦ oddPrimeSupport (product (start x R) (start y R) H (c i)))
  have htotal (i) : (left x y H R (c i)).card + (right x y H R (c i)).card ≤ K := by
    rw [total_card hx hy]
    exact hK i
  have hpool : q ∈ pool k (R - 1) (10 * (H + 1)) K := by
    apply (mem_pool k (R - 1) (10 * (H + 1)) K q).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro i
      refine ⟨(BoundedIntegerMotifs.subset_offsets _ _).mpr ?_, (Nat.le_add_right _ _).trans (htotal i)⟩
      intro z hz
      simpa only [hW] using left_bound hnew hamb old hold (c i) (hfree i) z hz
    · intro i
      refine ⟨(BoundedIntegerMotifs.subset_offsets _ _).mpr ?_, (Nat.le_add_left _ _).trans (htotal i)⟩
      intro z hz
      simpa only [hW] using right_bound hy hnew hamb old (c i) (hfree i) z hz
    · intro i
      exact coefficient_support hx hy hnew hamb old (c i) (hfree i)
  have hboth (i) := AsymmetricComponentOffsets.nonempty hx hy (c i) (hnon i)
  refine ⟨q, hpool, ⟨?_, ?_, fun i ↦ (hboth i).1, fun i ↦ (hboth i).2, htotal⟩, ?_⟩
  · exact fun _ _ hne ↦ left_disjoint hx _ _ (fun he ↦ hne (hcinj he))
  · exact fun _ _ hne ↦ right_disjoint hy _ _ (fun he ↦ hne (hcinj he))
  · choose w hw using (fun i ↦ AsymmetricComponentOffsets.square_roots hx hy (c i))
    exact ⟨w, hw⟩

open PaperP1.SplitRadicalPatternPool in
theorem exists_linear {x y L H R : ℕ} (hx : R < x) (hy : R < y)
    (hnew : L + 1 ≤ R) (hamb : 2 * R ≤ H) (old : Finset ℕ)
    (hold : ∀ n ∈ old, |(n : ℤ) - x| ≤ (R : ℤ)) (k a K : ℕ)
    (c : Fin k → (largePrimeGraph (start x R) (start y R) H).ConnectedComponent) (hcinj : Function.Injective c)
    (hfree : ∀ i, ¬ComponentPinned _ (pins x y L H R hnew hamb old) (c i))
    (hleft : ∀ i, (left x y H R (c i)).card = a)
    (hright : ∀ i, (right x y H R (c i)).card = 1) (hK : a + 1 ≤ K) :
    ∃ q ∈ pool k (R - 1) (10 * (H + 1)) K, SmoothDegreeOneHostCount.Valid a K q ∧
      ∃ w : Fin k → ℤ, ∀ i, w i ^ 2 = coefficient q i *
        integerProduct (q.1.1 i) (x : ℤ) * ((y : ℤ) + q.1.2 i) := by
  classical
  have hW : R - 1 + 1 = R := by omega
  have hexj (i) : ∃ j : ℤ, right x y H R (c i) = {j} := card_eq_one.mp (hright i)
  choose j hj using hexj
  have hI : Pairwise fun i t ↦ Disjoint (left x y H R (c i)) (left x y H R (c t)) :=
    fun _ _ hne ↦ left_disjoint hx _ _ (fun he ↦ hne (hcinj he))
  have hjinj : Function.Injective j := by
    intro i t heq
    by_contra hne
    have hd := right_disjoint hy (c i) (c t) (fun he ↦ hne (hcinj he))
    have hi : j i ∈ right x y H R (c i) := by rw [hj i]; exact mem_singleton_self _
    have ht : j i ∈ right x y H R (c t) := by rw [hj t, heq]; exact mem_singleton_self _
    exact disjoint_left.mp hd hi ht
  let q : Pattern k := ((fun i ↦ left x y H R (c i), j),
    fun i ↦ oddPrimeSupport (product (start x R) (start y R) H (c i)))
  have hpool : q ∈ pool k (R - 1) (10 * (H + 1)) K := by
    apply (mem_pool k (R - 1) (10 * (H + 1)) K q).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro i
      refine ⟨(BoundedIntegerMotifs.subset_offsets _ _).mpr ?_, ?_⟩
      · intro z hz
        simpa only [hW] using left_bound hnew hamb old hold (c i) (hfree i) z hz
      · change (left x y H R (c i)).card ≤ K
        rw [hleft i]
        omega
    · intro i
      have hsub : right x y H R (c i) ⊆ BoundedIntegerMotifs.offsets (R - 1 + 1) := by
        apply (BoundedIntegerMotifs.subset_offsets _ _).mpr
        intro z hz
        simpa only [hW] using right_bound hy hnew hamb old (c i) (hfree i) z hz
      exact hsub (by rw [hj i]; exact mem_singleton_self _)
    · intro i
      exact coefficient_support hx hy hnew hamb old (c i) (hfree i)
  refine ⟨q, hpool, ⟨hI, hjinj, hleft, ?_⟩, ?_⟩
  · intro i
    change (left x y H R (c i)).card + 1 ≤ K
    rw [hleft i]
    exact hK
  · have hroots (i) : ∃ w : ℤ, w ^ 2 = coefficient q i * integerProduct (q.1.1 i) (x : ℤ) * ((y : ℤ) + j i) := by
      obtain ⟨w, hw⟩ := AsymmetricComponentOffsets.square_roots hx hy (c i)
      rw [hj i, show integerProduct {j i} (y : ℤ) = (y : ℤ) + j i by simp only [integerProduct, prod_singleton]] at hw
      exact ⟨w, hw⟩
    choose w hw using hroots
    exact ⟨w, hw⟩

end PaperP1.AsymmetricComponentSystems
