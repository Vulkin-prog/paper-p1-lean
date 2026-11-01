module

public import PaperP1.Arithmetic.RoughValuePrimePool
public import PaperP1.Arithmetic.SignedPrimeSubsetTargets

/-! # Actual directed certificate graphs with an arbitrary fixed number of anchors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnchorCertificateGraph

open Finset PaperP1.LinearKernelFibres PaperP1.BoundedIntegerMotifs
  PaperP1.RoughValuePrimePool

abbrev Code (W t : ℕ) := Fin t → offsets W

def threshold (X W : ℕ) : ℕ := 2 * X * (offsets W).card

def order (X W : ℕ) (Y : ℝ) : ℕ := PaperP1.ShortPrimePassage.order (threshold X W) Y

def anchorValue {W t : ℕ} (x : ℕ) (c : Code W t) (i : Fin t) : ℕ := value x (c i).val

def receiverPool (W : ℕ) (Y : ℝ) (y : ℕ) : Finset ℕ := pool Y (fun u : offsets W ↦ value y u.val)

def Edge (X W t : ℕ) (Y : ℝ) (x y : ℕ) : Prop :=
  ∃ c : Code W t, ∃ T : Finset ℕ, T ⊆ pool Y (anchorValue x c) ∧
    T.card ≤ order X W Y ∧ threshold X W < T.prod id ∧
      ∀ p ∈ T, ∃ u : offsets W, p ∣ value y u.val

def outgoing (G : Finset ℕ) (X W t : ℕ) (Y : ℝ) (x : ℕ) : Finset ℕ := by
  classical
  exact G.filter (Edge X W t Y x)

def incoming (G : Finset ℕ) (X W t : ℕ) (Y : ℝ) (y : ℕ) : Finset ℕ := by
  classical
  exact G.filter fun x ↦ Edge X W t Y x y

theorem offset_bound (W : ℕ) (u : offsets W) : u.val.natAbs ≤ W :=
  (subset_offsets W {u.val}).mp (singleton_subset_iff.mpr u.property) _ (mem_singleton_self _)

theorem threshold_ge (X W : ℕ) : X ≤ threshold X W := by
  have hB : 1 ≤ (offsets W).card := by rw [offsets_card]; omega
  dsimp [threshold]
  nlinarith only [hB]

theorem value_height (X W x : ℕ) (u : offsets W) (hx : W < x ∧ x ≤ X) :
    0 < value x u.val ∧ value x u.val ≤ threshold X W := by
  have hu := offset_bound W u
  have hval := PaperP1.SmoothModulusHosts.value_cast x W u.val hx.1 hu
  have habs : |u.val| ≤ (W : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hu
  have hlo := (abs_le.mp habs).1
  have hxW : (W : ℤ) < x := by exact_mod_cast hx.1
  have hp : 0 < value x u.val := by omega
  have htri := Int.natAbs_add_le (x : ℤ) u.val
  rw [Int.natAbs_natCast] at htri
  have hvalue : value x u.val ≤ 2 * X := by dsimp [value]; omega
  have hB : 1 ≤ (offsets W).card := by rw [offsets_card]; omega
  exact ⟨hp, hvalue.trans (by
    dsimp [threshold]
    simpa only [mul_one] using Nat.mul_le_mul_left (2 * X) hB)⟩

theorem code_card (W t : ℕ) : Fintype.card (Code W t) = (2 * W + 1) ^ t := by
  simp only [Code, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, offsets_card]

theorem outgoing_count (G : Finset ℕ) (X W t x : ℕ) (Y : ℝ) (ht : 1 ≤ t) (hY : 1 < Y)
    (hG : ∀ n ∈ G, W < n ∧ n ≤ X) (hx : x ∈ G) :
    ((outgoing G X W t Y x).card : ℝ) ≤
      (2 * W + 1 : ℝ) ^ t * ((t : ℝ) * Real.exp 1 * (2 * W + 1 : ℝ)) ^ order X W Y := by
  classical
  let k := order X W Y
  let B := (offsets W).card
  let F := fun c : Code W t ↦ PaperP1.SignedPrimeSubsetTargets.targets G
    (pool Y (anchorValue x c)) k X (fun u : offsets W ↦ u.val)
  have hcover : ∀ y ∈ outgoing G X W t Y x, ∃ c ∈ (univ : Finset (Code W t)), y ∈ F c := by
    intro y hy
    obtain ⟨hyG, c, T, hTP, hcard, hprod, hreceiving⟩ := mem_filter.mp hy
    let f : T → offsets W := fun p ↦ Classical.choose (hreceiving p.val p.property)
    have hf : ∀ p : T, p.val ∣ value y (f p).val :=
      fun p ↦ Classical.choose_spec (hreceiving p.val p.property)
    refine ⟨c, mem_univ c, ?_⟩
    apply (PaperP1.SignedPrimeSubsetTargets.mem_targets G _ k X y _).mpr
    exact ⟨hyG, T, hTP, hcard, (threshold_ge X W).trans hprod.le, f, hf⟩
  have hF : ∀ c ∈ (univ : Finset (Code W t)), ((F c).card : ℝ) ≤
      ((t : ℝ) * Real.exp 1 * (B : ℝ)) ^ k := by
    intro c _
    have hpool := pool_order_bound Y (threshold X W) (anchorValue x c) hY (fun i ↦ by
      have hd := value_height X W x (c i) (hG x hx)
      exact ⟨hd.1, by exact_mod_cast hd.2⟩)
    have hpoolR : ((pool Y (anchorValue x c)).card : ℝ) ≤ (t : ℝ) * k := by
      have hpool' : (pool Y (anchorValue x c)).card ≤ t * k := by
        simpa only [Fintype.card_fin, k, order] using hpool
      exact_mod_cast hpool'
    have hB : (1 : ℝ) ≤ B := by dsimp [B]; rw [offsets_card]; push_cast; linarith
    have hbound := PaperP1.SignedPrimeSubsetTargets.targets_count G (pool Y (anchorValue x c)) k X W
      (fun u : offsets W ↦ u.val) hG (fun p hp ↦ (pool_data Y _ p hp).1) (offset_bound W)
    have hweight := PaperP1.BoundedSubsetWeights.weightSum_le_of_card_le
      (pool Y (anchorValue x c)) B t k hB (by exact_mod_cast ht) hpoolR
    exact hbound.trans (by simpa only [Fintype.card_coe, mul_assoc, mul_comm, mul_left_comm] using hweight)
  have hcount := PaperP1.FiniteCoverCount.cardinal_le (outgoing G X W t Y x)
    (univ : Finset (Code W t)) F _ hcover hF
  simpa only [card_univ, code_card, Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one, B, offsets_card] using hcount

theorem incoming_count (G : Finset ℕ) (X W t y : ℕ) (Y : ℝ) (ht : 1 ≤ t) (hY : 1 < Y)
    (hG : ∀ n ∈ G, W < n ∧ n ≤ X) (hy : y ∈ G) :
    ((incoming G X W t Y y).card : ℝ) ≤
      (2 * W + 1 : ℝ) ^ t * ((t : ℝ) * Real.exp 1 * (2 * W + 1 : ℝ)) ^ order X W Y := by
  classical
  let k := order X W Y
  let B := (offsets W).card
  let P := receiverPool W Y y
  let F := fun c : Code W t ↦ PaperP1.SignedPrimeSubsetTargets.targets G P k X (fun i : Fin t ↦ (c i).val)
  have hP : ∀ p ∈ P, p.Prime ∧ Y < (p : ℝ) := fun p hp ↦
    ⟨(pool_data Y _ p hp).1, (pool_data Y _ p hp).2.1⟩
  have hcover : ∀ x ∈ incoming G X W t Y y, ∃ c ∈ (univ : Finset (Code W t)), x ∈ F c := by
    intro x hx
    obtain ⟨hxG, c, T, hTP, hcard, hprod, hreceiving⟩ := mem_filter.mp hx
    have hTrecv : T ⊆ P := by
      intro p hp
      obtain ⟨u, hu⟩ := hreceiving p hp
      have hpd := pool_data Y _ p (hTP hp)
      exact mem_biUnion.mpr ⟨u, mem_univ u, mem_filter.mpr
        ⟨Nat.mem_primeFactors.mpr ⟨hpd.1, hu, (value_height X W y u (hG y hy)).1.ne'⟩, hpd.2.1⟩⟩
    have hsource : ∀ p : T, ∃ i : Fin t, p.val ∣ anchorValue x c i :=
      fun p ↦ (pool_data Y _ p.val (hTP p.property)).2.2
    let f : T → Fin t := fun p ↦ Classical.choose (hsource p)
    have hf : ∀ p : T, p.val ∣ value x (c (f p)).val := fun p ↦ Classical.choose_spec (hsource p)
    refine ⟨c, mem_univ c, ?_⟩
    apply (PaperP1.SignedPrimeSubsetTargets.mem_targets G P k X x _).mpr
    exact ⟨hxG, T, hTrecv, hcard, (threshold_ge X W).trans hprod.le, f, hf⟩
  have hpool := pool_order_bound Y (threshold X W) (fun u : offsets W ↦ value y u.val) hY (fun u ↦ by
    have hd := value_height X W y u (hG y hy)
    exact ⟨hd.1, by exact_mod_cast hd.2⟩)
  have hpoolR : (P.card : ℝ) ≤ (B : ℝ) * k := by
    have hpool' : P.card ≤ B * k := by
      simpa only [Fintype.card_coe, P, receiverPool, B, k, order] using hpool
    exact_mod_cast hpool'
  have hB : (1 : ℝ) ≤ B := by dsimp [B]; rw [offsets_card]; push_cast; linarith
  have hF : ∀ c ∈ (univ : Finset (Code W t)), ((F c).card : ℝ) ≤
      ((t : ℝ) * Real.exp 1 * (B : ℝ)) ^ k := by
    intro c _
    have hbound := PaperP1.SignedPrimeSubsetTargets.targets_count G P k X W
      (fun i : Fin t ↦ (c i).val) hG (fun p hp ↦ (hP p hp).1) (fun i ↦ offset_bound W (c i))
    have hweight := PaperP1.BoundedSubsetWeights.weightSum_le_of_card_le P t B k
      (by exact_mod_cast ht) hB hpoolR
    exact hbound.trans (by simpa only [Fintype.card_fin] using hweight)
  have hcount := PaperP1.FiniteCoverCount.cardinal_le (incoming G X W t Y y)
    (univ : Finset (Code W t)) F _ hcover hF
  simpa only [card_univ, code_card, Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one, B, offsets_card] using hcount

end PaperP1.AnchorCertificateGraph
