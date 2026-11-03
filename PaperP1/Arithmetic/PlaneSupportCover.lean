module

public import PaperP1.Arithmetic.FreePlaneCRT
public import PaperP1.Arithmetic.CRTSupportCover

/-! # First-passage factor certificates on an arbitrary finite family of genuine real planes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlaneSupportCover

open Finset PaperP1.OffsetFactorSupports

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

abbrev Plane := (Fin 3 → ℝ) × ℝ

def fibre {s : ℕ} (base : Fin 3 → ℕ) (width : ℕ) (q : Fin s → ℕ)
    (w : Fin s → Fin 2 → ℤ) (P : Plane) (k : Fin 3) : Finset (Fin 3 → ℕ) :=
  (CRTProductCover.box 3 base width).filter fun X ↦
    Pairwise (fun i j ↦ Nat.Coprime (q i) (q j)) ∧ P.1 k ≠ 0 ∧
      (∑ i, P.1 i * (X i : ℝ)) = P.2 ∧
        ∀ j i, (q j : ℤ) ∣ (X (k.succAbove i) : ℤ) + w j i

def centres (base : Fin 3 → ℕ) (width R : ℕ) (A : Finset ℕ) (P : Plane) (k : Fin 3) :
    Finset (Fin 3 → ℕ) :=
  (CRTProductCover.offsets A.card 2 R).biUnion fun w ↦ fibre base width (CRTSupportCover.sizes A) w P k

def planeCentres (base : Fin 3 → ℕ) (width R : ℕ) (A : Finset ℕ) (planes : Finset Plane) :
    Finset (Fin 3 → ℕ) := (planes ×ˢ univ).biUnion fun c ↦ centres base width R A c.1 c.2

def certificates (base : Fin 3 → ℕ) (N D R : ℕ) (Y X : ℝ) (planes : Finset Plane) :
    Finset (Fin 3 → ℕ) :=
  ((integerSupports Y X).filter fun A ↦ (N : ℝ) < (A.prod id : ℕ)).biUnion
    fun A ↦ planeCentres base (D * N) R A planes

theorem mem_fibre {s : ℕ} (base : Fin 3 → ℕ) (width : ℕ) (q : Fin s → ℕ)
    (w : Fin s → Fin 2 → ℤ) (P : Plane) (k : Fin 3) (X : Fin 3 → ℕ) :
    X ∈ fibre base width q w P k ↔ (∀ i, X i ∈ Ico (base i) (base i + width)) ∧
      Pairwise (fun i j ↦ Nat.Coprime (q i) (q j)) ∧ P.1 k ≠ 0 ∧
        (∑ i, P.1 i * (X i : ℝ)) = P.2 ∧
          ∀ j i, (q j : ℤ) ∣ (X (k.succAbove i) : ℤ) + w j i := by
  simp only [fibre, mem_filter, CRTProductCover.box, Fintype.mem_piFinset]

theorem fibre_real_card {s : ℕ} (base : Fin 3 → ℕ) (width : ℕ) (q : Fin s → ℕ)
    (w : Fin s → Fin 2 → ℤ) (P : Plane) (k : Fin 3) :
    ((fibre base width q w P k).card : ℝ) ≤ ((width : ℝ) / (∏ j, q j : ℕ) + 1) ^ 2 := by
  by_cases hf : (fibre base width q w P k).Nonempty
  · obtain ⟨X₀, hX₀⟩ := hf
    obtain ⟨_hbox, hcop, hA, _hplane, _hdiv⟩ := (mem_fibre base width q w P k X₀).mp hX₀
    apply FreePlaneCRT.card_real_bound _ base width q w hcop P.1 P.2 k hA
    · intro X hX
      exact ((mem_fibre base width q w P k X).mp hX).2.2.2.1
    · intro X hX
      exact ((mem_fibre base width q w P k X).mp hX).1
    · intro X hX
      exact ((mem_fibre base width q w P k X).mp hX).2.2.2.2
  · rw [not_nonempty_iff_eq_empty.mp hf, card_empty, Nat.cast_zero]
    positivity

theorem centres_card (base : Fin 3 → ℕ) (width R : ℕ) (A : Finset ℕ) (P : Plane) (k : Fin 3) :
    ((centres base width R A P k).card : ℝ) ≤
      (2 * R + 1 : ℕ) ^ (2 * A.card) * ((width : ℝ) / (A.prod id : ℕ) + 1) ^ 2 := by
  have h := FiniteCoverCount.cardinal_le (centres base width R A P k) (CRTProductCover.offsets A.card 2 R)
    (fun w ↦ fibre base width (CRTSupportCover.sizes A) w P k)
    (((width : ℝ) / (A.prod id : ℕ) + 1) ^ 2) (fun X hX ↦ mem_biUnion.mp hX) (by
      intro w _
      simpa only [CRTSupportCover.product_sizes] using fibre_real_card base width (CRTSupportCover.sizes A) w P k)
  simpa only [CRTProductCover.offsets_card, Nat.cast_pow] using h

theorem short_product_bound (base : Fin 3 → ℕ) (N D R : ℕ) (A : Finset ℕ) (P : Plane) (k : Fin 3)
    (hN : 1 ≤ N) (hprod : (N : ℝ) < (A.prod id : ℕ)) :
    ((centres base (D * N) R A P k).card : ℝ) ≤ (2 * R + 1 : ℕ) ^ (2 * A.card) * (D + 1 : ℝ) ^ 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hp : (0 : ℝ) < (A.prod id : ℕ) := hn.trans hprod
  have hdiv : (D * N : ℕ) / ((A.prod id : ℕ) : ℝ) ≤ (D : ℝ) := by
    apply (div_le_iff₀ hp).mpr
    simpa only [Nat.cast_mul] using mul_le_mul_of_nonneg_left hprod.le (Nat.cast_nonneg D)
  exact (centres_card base (D * N) R A P k).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (add_le_add hdiv le_rfl) 2) (by positivity))

theorem plane_centres_card (base : Fin 3 → ℕ) (N D R : ℕ) (A : Finset ℕ) (planes : Finset Plane)
    (hN : 1 ≤ N) (hprod : (N : ℝ) < (A.prod id : ℕ)) :
    ((planeCentres base (D * N) R A planes).card : ℝ) ≤
      3 * planes.card * (D + 1 : ℝ) ^ 2 * (2 * R + 1 : ℕ) ^ (2 * A.card) := by
  have h := FiniteCoverCount.cardinal_le (planeCentres base (D * N) R A planes) (planes ×ˢ (univ : Finset (Fin 3)))
    (fun c ↦ centres base (D * N) R A c.1 c.2) ((2 * R + 1 : ℕ) ^ (2 * A.card) * (D + 1 : ℝ) ^ 2)
    (fun X hX ↦ mem_biUnion.mp hX) (fun c _ ↦ short_product_bound base N D R A c.1 c.2 hN hprod)
  simpa only [card_product, card_univ, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat, mul_assoc,
    mul_left_comm, mul_comm] using h

theorem certificate_card (base : Fin 3 → ℕ) (N D R : ℕ) (Y X : ℝ) (planes : Finset Plane) (hN : 1 ≤ N) :
    ((certificates base N D R Y X planes).card : ℝ) ≤
      3 * planes.card * (D + 1 : ℝ) ^ 2 * integerWeightedCount Y X (((2 * R + 1 : ℕ) : ℝ) ^ 2) := by
  let pool := (integerSupports Y X).filter fun A ↦ (N : ℝ) < (A.prod id : ℕ)
  calc
    _ ≤ ∑ A ∈ pool, ((planeCentres base (D * N) R A planes).card : ℝ) := by
      have hnat : (certificates base N D R Y X planes).card ≤ ∑ A ∈ pool, (planeCentres base (D * N) R A planes).card :=
        card_biUnion_le
      exact_mod_cast hnat
    _ ≤ ∑ A ∈ pool, 3 * planes.card * (D + 1 : ℝ) ^ 2 * (2 * R + 1 : ℕ) ^ (2 * A.card) :=
      sum_le_sum (fun A hA ↦ plane_centres_card base N D R A planes hN (mem_filter.mp hA).2)
    _ = (3 * planes.card * (D + 1 : ℝ) ^ 2) * ∑ A ∈ pool, (((2 * R + 1 : ℕ) : ℝ) ^ 2) ^ A.card := by
      rw [mul_sum]
      apply sum_congr rfl
      intro A _
      rw [← pow_mul]
    _ ≤ (3 * planes.card * (D + 1 : ℝ) ^ 2) * ∑ A ∈ integerSupports Y X, (((2 * R + 1 : ℕ) : ℝ) ^ 2) ^ A.card :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)) (by positivity)
    _ = _ := rfl

theorem mem_centres_of (base : Fin 3 → ℕ) (width R : ℕ) (A : Finset ℕ) (P : Plane) (k : Fin 3)
    (X : Fin 3 → ℕ) (hbox : ∀ i, X i ∈ Ico (base i) (base i + width)) (hA : P.1 k ≠ 0)
    (hplane : (∑ i, P.1 i * (X i : ℝ)) = P.2)
    (hcop : ∀ g ∈ A, ∀ h ∈ A, g ≠ h → Nat.Coprime g h)
    (hdiv : ∀ g ∈ A, ∃ w : Fin 3 → ℤ, (∀ i, (w i).natAbs ≤ R) ∧
      ∀ i, (g : ℤ) ∣ (X i : ℤ) + w i) : X ∈ centres base width R A P k := by
  have hdata (j : Fin A.card) := hdiv (CRTSupportCover.sizes A j) (CRTSupportCover.sizes_mem A j)
  choose v hv hvdiv using hdata
  let w : Fin A.card → Fin 2 → ℤ := fun j i ↦ v j (k.succAbove i)
  have hw : ∀ j i, (w j i).natAbs ≤ R := fun j i ↦ hv j (k.succAbove i)
  have hcop' : Pairwise (fun i j ↦ Nat.Coprime (CRTSupportCover.sizes A i) (CRTSupportCover.sizes A j)) := by
    intro i j hij
    exact hcop _ (CRTSupportCover.sizes_mem A i) _ (CRTSupportCover.sizes_mem A j)
      (fun heq ↦ hij (CRTSupportCover.sizes_injective A heq))
  exact mem_biUnion.mpr ⟨w, (CRTProductCover.mem_offsets A.card 2 R w).mpr hw,
    (mem_fibre base width _ w P k X).mpr ⟨hbox, hcop', hA, hplane, fun j i ↦ hvdiv j (k.succAbove i)⟩⟩

theorem mem_certificates_of (base : Fin 3 → ℕ) (N D R : ℕ) (Y V : ℝ) (planes : Finset Plane)
    (X : Fin 3 → ℕ) (hbox : ∀ i, X i ∈ Ico (base i) (base i + D * N))
    (A : Finset ℕ) (hA : A ∈ integerSupports Y V) (hlarge : (N : ℝ) < (A.prod id : ℕ))
    (hcop : ∀ g ∈ A, ∀ h ∈ A, g ≠ h → Nat.Coprime g h)
    (hdiv : ∀ g ∈ A, ∃ w : Fin 3 → ℤ, (∀ i, (w i).natAbs ≤ R) ∧ ∀ i, (g : ℤ) ∣ (X i : ℤ) + w i)
    (hplane : ∃ P ∈ planes, P.1 ≠ 0 ∧ (∑ i, P.1 i * (X i : ℝ)) = P.2) :
    X ∈ certificates base N D R Y V planes := by
  obtain ⟨P, hP, hnormal, hplane⟩ := hplane
  have hcoord : ∃ k, P.1 k ≠ 0 := by
    by_contra hnot
    apply hnormal
    funext i
    exact not_ne_iff.mp (not_exists.mp hnot i)
  obtain ⟨k, hk⟩ := hcoord
  exact mem_biUnion.mpr ⟨A, mem_filter.mpr ⟨hA, hlarge⟩,
    mem_biUnion.mpr ⟨(P, k), mem_product.mpr ⟨hP, mem_univ _⟩,
      mem_centres_of base (D * N) R A P k X hbox hk hplane hcop hdiv⟩⟩

theorem restrict_centres (base : Fin 3 → ℕ) (width R : ℕ) (A : Finset ℕ) (P : Plane) (k : Fin 3)
    (X : Fin 3 → ℕ) (hX : X ∈ CRTSupportCover.centres base width R A) (hA : P.1 k ≠ 0)
    (hplane : (∑ i, P.1 i * (X i : ℝ)) = P.2) : X ∈ centres base width R A P k := by
  obtain ⟨v, hv, hXv⟩ := mem_biUnion.mp hX
  obtain ⟨hbox, hcop, hdiv⟩ := (CRTProductCover.mem_fibre base width (CRTSupportCover.sizes A) v X).mp hXv
  let w : Fin A.card → Fin 2 → ℤ := fun j i ↦ v j (k.succAbove i)
  have hw : ∀ j i, (w j i).natAbs ≤ R := fun j i ↦
    ((CRTProductCover.mem_offsets A.card 3 R v).mp hv) j (k.succAbove i)
  exact mem_biUnion.mpr ⟨w, (CRTProductCover.mem_offsets A.card 2 R w).mpr hw,
    (mem_fibre base width _ w P k X).mpr ⟨hbox, hcop, hA, hplane, fun j i ↦ hdiv j (k.succAbove i)⟩⟩

theorem restrict_certificates (base : Fin 3 → ℕ) (N D R : ℕ) (Y V : ℝ) (planes : Finset Plane)
    (X : Fin 3 → ℕ) (hX : X ∈ CRTSupportCover.certificates base N D R Y V)
    (hplane : ∃ P ∈ planes, P.1 ≠ 0 ∧ (∑ i, P.1 i * (X i : ℝ)) = P.2) :
    X ∈ certificates base N D R Y V planes := by
  obtain ⟨A, hA, hXA⟩ := mem_biUnion.mp hX
  obtain ⟨P, hP, hnormal, hplane⟩ := hplane
  have hcoord : ∃ k, P.1 k ≠ 0 := by
    by_contra hnot
    apply hnormal
    funext i
    exact not_ne_iff.mp (not_exists.mp hnot i)
  obtain ⟨k, hk⟩ := hcoord
  exact mem_biUnion.mpr ⟨A, hA, mem_biUnion.mpr ⟨(P, k), mem_product.mpr ⟨hP, mem_univ _⟩,
    restrict_centres base (D * N) R A P k X hXA hk hplane⟩⟩

end PaperP1.PlaneSupportCover
