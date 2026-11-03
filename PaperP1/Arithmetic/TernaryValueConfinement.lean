module

public import PaperP1.Arithmetic.ProductConfinement
public import PaperP1.Arithmetic.TernaryTopProducts
public import PaperP1.Arithmetic.CRTSupportCover

/-! # Large actual support groups give confinement or a bounded product certificate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryValueConfinement

open Finset PaperP1.TernaryPrimeGroups PaperP1.TernaryTopProducts

def values (U : Fin 3 → Finset ℕ) (H : ℕ) : Finset ℕ := (active U H).image (group H)

def largeValues (U : Fin 3 → Finset ℕ) (H : ℕ) (Y : ℝ) : Finset ℕ := by
  classical
  exact (values U H).filter fun g : ℕ ↦ Y < (g : ℝ)

def largeSupports (U : Fin 3 → Finset ℕ) (H : ℕ) (Y : ℝ) : Finset (Fin 3 → ℕ) := by
  classical
  exact (active U H).filter fun u ↦ Y < (group H u : ℝ)

theorem mem_values (U : Fin 3 → Finset ℕ) (H g : ℕ) :
    g ∈ values U H ↔ ∃ u ∈ active U H, group H u = g := mem_image

theorem large_image (U : Fin 3 → Finset ℕ) (H : ℕ) (Y : ℝ) :
    (largeSupports U H Y).image (group H) = largeValues U H Y := by
  classical
  ext g
  constructor
  · intro hg
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hg
    obtain ⟨hum, hug⟩ := mem_filter.mp hu
    exact mem_filter.mpr ⟨mem_image_of_mem _ hum, hug⟩
  · intro hg
    obtain ⟨hgm, hgY⟩ := mem_filter.mp hg
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hgm
    exact mem_image.mpr ⟨u, mem_filter.mpr ⟨hu, hgY⟩, rfl⟩

theorem large_card {U : Fin 3 → Finset ℕ} {H : ℕ}
    (hwidth : ∀ i, ∀ n ∈ U i, ∀ m ∈ U i, ((n : ℤ) - m).natAbs ≤ H) (Y : ℝ) :
    (largeSupports U H Y).card = (largeValues U H Y).card := by
  classical
  rw [← large_image]
  exact (card_image_of_injOn ((active_values_injective hwidth).mono (filter_subset _ _))).symm

theorem coprime_values {U : Fin 3 → Finset ℕ} {H : ℕ}
    (hwidth : ∀ i, ∀ n ∈ U i, ∀ m ∈ U i, ((n : ℤ) - m).natAbs ≤ H)
    {g h : ℕ} (hg : g ∈ values U H) (hh : h ∈ values U H) (hne : g ≠ h) : Nat.Coprime g h := by
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hg
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hh
  exact group_coprime hwidth (mem_filter.mp hu).1 (mem_filter.mp hv).1 (fun heq ↦ hne (congrArg (group H) heq))

theorem selected_values_le_top {U : Fin 3 → Finset ℕ} {H k : ℕ}
    (hwidth : ∀ i, ∀ n ∈ U i, ∀ m ∈ U i, ((n : ℤ) - m).natAbs ≤ H)
    (A : Finset ℕ) (hA : A ⊆ values U H) (hcard : A.card = k) :
    A.prod id ≤ topProduct U H k := by
  classical
  let S := (active U H).filter fun u ↦ group H u ∈ A
  have hS : S ⊆ active U H := filter_subset _ _
  have hinj : Set.InjOn (group H) S := (active_values_injective hwidth).mono hS
  have himage : S.image (group H) = A := by
    ext g
    constructor
    · intro hg
      obtain ⟨u, hu, rfl⟩ := mem_image.mp hg
      exact (mem_filter.mp hu).2
    · intro hg
      obtain ⟨u, hu, rfl⟩ := mem_image.mp (hA hg)
      exact mem_image.mpr ⟨u, mem_filter.mpr ⟨hu, hg⟩, rfl⟩
  have hScard : S.card = k := by rw [← card_image_of_injOn hinj, himage]; exact hcard
  have hprod : (S.image (group H)).prod id = ∏ u ∈ S, group H u := by
    rw [prod_image hinj]
    rfl
  rw [himage] at hprod
  rw [hprod]
  exact selected_le_top U H k S hS hScard

theorem confinement_or_certificate {U : Fin 3 → Finset ℕ} {H k : ℕ}
    (hwidth : ∀ i, ∀ n ∈ U i, ∀ m ∈ U i, ((n : ℤ) - m).natAbs ≤ H)
    (Y N : ℝ) (hY : 1 < Y) (hN : 1 ≤ N) (hk : 1 ≤ k)
    (htop : (topProduct U H k : ℝ) ≤ N) :
    (largeSupports U H Y).card ≤ k - 1 + ⌊Real.log N / Real.log Y⌋₊ ∨
      ∃ A ⊆ largeValues U H Y, (∀ g ∈ A, (g : ℝ) ≤ N ^ (1 / (k : ℝ))) ∧
        N < (A.prod id : ℕ) ∧ (A.prod id : ℕ) ≤ N ^ (1 + 1 / (k : ℝ)) := by
  classical
  have hselected (A : Finset ℕ) (hA : A ⊆ largeValues U H Y) (hcard : A.card = k) :
      (A.prod id : ℕ) ≤ N := by
    exact (show ((A.prod id : ℕ) : ℝ) ≤ topProduct U H k by
      exact_mod_cast selected_values_le_top hwidth A (hA.trans (filter_subset _ _)) hcard).trans htop
  have h := ProductConfinement.confinement_or_certificate (largeValues U H Y) Y N hY hN k hk
    (fun _ hg ↦ (mem_filter.mp hg).2) hselected
  rwa [large_card hwidth Y]

theorem certificate_mem {U : Fin 3 → Finset ℕ} {H R N D : ℕ} (X : Fin 3 → ℕ)
    (hwidth : ∀ i, ∀ n ∈ U i, ∀ m ∈ U i, ((n : ℤ) - m).natAbs ≤ H)
    (hoff : ∀ i, ∀ n ∈ U i, ((n : ℤ) - X i).natAbs ≤ R)
    (base : Fin 3 → ℕ) (hbox : ∀ i, X i ∈ Ico (base i) (base i + D * N))
    (Y V : ℝ) (hY : 1 ≤ Y) (hV : 0 ≤ V)
    (A : Finset ℕ) (hA : A ⊆ largeValues U H Y)
    (hlarge : (N : ℝ) < (A.prod id : ℕ)) (hsmall : (A.prod id : ℕ) ≤ V) :
    X ∈ CRTSupportCover.certificates base N D R Y V := by
  classical
  apply mem_biUnion.mpr
  refine ⟨A, mem_filter.mpr ⟨?_, hlarge⟩, ?_⟩
  · apply (OffsetFactorSupports.mem_integerSupports Y V hY hV A).mpr
    exact ⟨fun _ hg ↦ (mem_filter.mp (hA hg)).2, hsmall⟩
  · apply CRTSupportCover.mem_centres_of base (D * N) R A X hbox
    · intro g hg h hh hne
      exact coprime_values hwidth (mem_filter.mp (hA hg)).1 (mem_filter.mp (hA hh)).1 hne
    · intro g hg
      obtain ⟨u, hu, rfl⟩ := mem_image.mp (mem_filter.mp (hA hg)).1
      have hum := ((mem_active U H u).mp hu).1
      refine ⟨fun i ↦ (u i : ℤ) - X i, fun i ↦ hoff i (u i) (hum i), ?_⟩
      intro i
      have heq : (X i : ℤ) + ((u i : ℤ) - X i) = u i := by ring
      rw [heq]
      exact Int.natCast_dvd_natCast.mpr (group_dvd_value H u i)

end PaperP1.TernaryValueConfinement
