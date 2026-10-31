module

public import PaperP1.Arithmetic.ProductCertificate
public import PaperP1.Arithmetic.DivisorSubpolynomial
public import PaperP1.Asymptotics.CriticalBandScale

/-! # Product certificates for the actual fixed source windows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedSourceCertificate

open Finset PaperP1.ProductCertificate

def sourceValues {s : ℕ} (x : Fin s → ℕ) (B : ℕ) (a : Fin s × Fin B) : ℕ :=
  x a.1 - 1 + a.2.val

def certificateTargets {s : ℕ} (x : Fin s → ℕ) (L k N : ℕ) : Finset ℕ :=
  targets (sourceValues x (L + 1)) (L + 1) k N N

def HasStrictCertificate {s : ℕ} (x : Fin s → ℕ) (L k N z : ℕ) : Prop :=
  ∃ G w : Fin k → ℕ,
    (∀ i, 1 < G i ∧ ∃ a : Fin s, ∃ u : Fin (L + 1), G i ∣ x a - 1 + u.val) ∧
    (∀ i, w i < L + 1) ∧ Pairwise (fun i j ↦ Nat.Coprime (G i) (G j)) ∧
    N < ∏ i, G i ∧ ∀ i, G i ∣ z - 1 + w i

def HasIntegerCertificate {s : ℕ} (x : Fin s → ℕ) (L k N z : ℕ) : Prop :=
  ∃ G : Fin k → ℕ,
    (∀ i, 1 < G i ∧ ∃ a : Fin s, ∃ u : ℤ,
      -1 ≤ u ∧ u ≤ (L : ℤ) - 1 ∧ (G i : ℤ) ∣ (x a : ℤ) + u) ∧
    Pairwise (fun i j ↦ Nat.Coprime (G i) (G j)) ∧ N < ∏ i, G i ∧
    ∀ i, ∃ w : ℤ, -1 ≤ w ∧ w ≤ (L : ℤ) - 1 ∧ (G i : ℤ) ∣ (z : ℤ) + w

def sourceTargets {s : ℕ} (x : Fin s → ℕ) (L k N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico N (2 * N)).filter (HasStrictCertificate x L k N)

theorem sourceValues_pos {s N L : ℕ} (x : Fin s → ℕ) (hN : 2 ≤ N)
    (hx : ∀ a, x a ∈ Finset.Ico N (2 * N)) (a : Fin s × Fin (L + 1)) :
    0 < sourceValues x (L + 1) a := by
  have hxa := (mem_Ico.mp (hx a.1)).1
  dsimp [sourceValues]
  omega

theorem sourceValues_le_square {s N L : ℕ} (x : Fin s → ℕ) (hN : 3 ≤ N)
    (hL : L ≤ N) (hx : ∀ a, x a ∈ Finset.Ico N (2 * N)) (a : Fin s × Fin (L + 1)) :
    sourceValues x (L + 1) a ≤ N ^ 2 := by
  have hxa := mem_Ico.mp (hx a.1)
  have hua := a.2.isLt
  have hsmall : sourceValues x (L + 1) a ≤ 3 * N := by dsimp [sourceValues]; omega
  exact hsmall.trans (by nlinarith)

theorem mem_certificateTargets {s : ℕ} (x : Fin s → ℕ) (L k N z : ℕ)
    (hN : 2 ≤ N) (hx : ∀ a, x a ∈ Finset.Ico N (2 * N)) :
    z ∈ certificateTargets x L k N ↔ z ∈ Finset.Ico N (2 * N) ∧
      ∃ G w : Fin k → ℕ,
        (∀ i, 1 < G i ∧ ∃ a : Fin s, ∃ u : Fin (L + 1), G i ∣ x a - 1 + u.val) ∧
        (∀ i, w i < L + 1) ∧ Pairwise (fun i j ↦ Nat.Coprime (G i) (G j)) ∧
        N ≤ ∏ i, G i ∧ ∀ i, G i ∣ z - 1 + w i := by
  simpa only [certificateTargets, sourceValues, Prod.exists, two_mul] using
    mem_targets (sourceValues x (L + 1)) (sourceValues_pos x hN hx) (L + 1) k N N z

theorem mem_sourceTargets {s : ℕ} (x : Fin s → ℕ) (L k N z : ℕ) :
    z ∈ sourceTargets x L k N ↔ z ∈ Finset.Ico N (2 * N) ∧ HasStrictCertificate x L k N z := by
  classical
  exact mem_filter

theorem sourceTargets_subset {s : ℕ} (x : Fin s → ℕ) (L k N : ℕ)
    (hN : 2 ≤ N) (hx : ∀ a, x a ∈ Finset.Ico N (2 * N)) :
    sourceTargets x L k N ⊆ certificateTargets x L k N := by
  intro z hz
  obtain ⟨hz, G, w, hG, hw, hcop, hprod, hdiv⟩ := (mem_sourceTargets x L k N z).mp hz
  exact (mem_certificateTargets x L k N z hN hx).mpr ⟨hz, G, w, hG, hw, hcop, hprod.le, hdiv⟩

theorem exists_offset_index (L : ℕ) (w : ℤ) (hwlo : -1 ≤ w) (hwhi : w ≤ (L : ℤ) - 1) :
    ∃ u : Fin (L + 1), (u.val : ℤ) - 1 = w := by
  have hpos : 0 ≤ w + 1 := by omega
  refine ⟨⟨(w + 1).toNat, ?_⟩, ?_⟩
  · omega
  · change (((w + 1).toNat : ℕ) : ℤ) - 1 = w
    omega

theorem offset_value (x L : ℕ) (hx : 1 ≤ x) (u : Fin (L + 1)) :
    ((x - 1 + u.val : ℕ) : ℤ) = (x : ℤ) + ((u.val : ℤ) - 1) := by omega

theorem offset_index_bounds (L : ℕ) (u : Fin (L + 1)) :
    (-1 : ℤ) ≤ (u.val : ℤ) - 1 ∧ (u.val : ℤ) - 1 ≤ (L : ℤ) - 1 := by
  have := u.isLt
  omega

theorem offset_dvd_iff (g x L : ℕ) (hx : 1 ≤ x) (u : Fin (L + 1)) :
    g ∣ x - 1 + u.val ↔ (g : ℤ) ∣ (x : ℤ) + ((u.val : ℤ) - 1) := by
  rw [← offset_value x L hx u, Int.natCast_dvd_natCast]

theorem hasIntegerCertificate_iff {s : ℕ} (x : Fin s → ℕ) (L k N z : ℕ)
    (hx : ∀ a, 1 ≤ x a) (hz : 1 ≤ z) :
    HasIntegerCertificate x L k N z ↔ HasStrictCertificate x L k N z := by
  classical
  constructor
  · rintro ⟨G, hG, hcop, hprod, htarget⟩
    have hGnat (i : Fin k) : 1 < G i ∧ ∃ a : Fin s, ∃ u : Fin (L + 1),
        G i ∣ x a - 1 + u.val := by
      obtain ⟨hGi, a, u, hu, huL, hdiv⟩ := hG i
      obtain ⟨uindex, hindex⟩ := exists_offset_index L u hu huL
      refine ⟨hGi, a, uindex, (offset_dvd_iff (G i) (x a) L (hx a) uindex).mpr ?_⟩
      simpa only [hindex] using hdiv
    have htargetNat (i : Fin k) : ∃ w : ℕ, w < L + 1 ∧ G i ∣ z - 1 + w := by
      obtain ⟨w, hw, hwL, hdiv⟩ := htarget i
      obtain ⟨windex, hindex⟩ := exists_offset_index L w hw hwL
      refine ⟨windex.val, windex.isLt, (offset_dvd_iff (G i) z L hz windex).mpr ?_⟩
      simpa only [hindex] using hdiv
    choose w hw using htargetNat
    exact ⟨G, w, hGnat, (fun i ↦ (hw i).1), hcop, hprod, (fun i ↦ (hw i).2)⟩
  · rintro ⟨G, w, hG, hw, hcop, hprod, htarget⟩
    refine ⟨G, ?_, hcop, hprod, ?_⟩
    · intro i
      obtain ⟨hGi, a, u, hdiv⟩ := hG i
      exact ⟨hGi, a, (u.val : ℤ) - 1, (offset_index_bounds L u).1,
        (offset_index_bounds L u).2, (offset_dvd_iff (G i) (x a) L (hx a) u).mp hdiv⟩
    · intro i
      let wi : Fin (L + 1) := ⟨w i, hw i⟩
      exact ⟨(wi.val : ℤ) - 1, (offset_index_bounds L wi).1, (offset_index_bounds L wi).2,
        (offset_dvd_iff (G i) z L hz wi).mp (htarget i)⟩

theorem mem_sourceTargets_integer {s : ℕ} (x : Fin s → ℕ) (L k N z : ℕ)
    (hN : 2 ≤ N) (hx : ∀ a, x a ∈ Finset.Ico N (2 * N)) :
    z ∈ sourceTargets x L k N ↔ z ∈ Finset.Ico N (2 * N) ∧ HasIntegerCertificate x L k N z := by
  have hxpos : ∀ a, 1 ≤ x a := fun a ↦ (by have := (mem_Ico.mp (hx a)).1; omega)
  rw [mem_sourceTargets]
  constructor
  · rintro ⟨hz, hcert⟩
    have hzpos : 1 ≤ z := by have := (mem_Ico.mp hz).1; omega
    exact ⟨hz, (hasIntegerCertificate_iff x L k N z hxpos hzpos).mpr hcert⟩
  · rintro ⟨hz, hcert⟩
    have hzpos : 1 ≤ z := by have := (mem_Ico.mp hz).1; omega
    exact ⟨hz, (hasIntegerCertificate_iff x L k N z hxpos hzpos).mp hcert⟩

theorem finite_real_bound {s : ℕ} (x : Fin s → ℕ) (L k N : ℕ) (hN : 1 ≤ N)
    (D : ℝ) (_hD : 0 ≤ D)
    (hdiv : ∀ a : Fin s × Fin (L + 1), ((sourceValues x (L + 1) a).divisors.card : ℝ) ≤ D) :
    ((certificateTargets x L k N).card : ℝ) ≤
      (s : ℝ) ^ k * (L + 1 : ℝ) ^ (2 * k) * D ^ k := by
  have hsum : ((∑ a : Fin s × Fin (L + 1), (sourceValues x (L + 1) a).divisors.card : ℕ) : ℝ) ≤
      (s : ℝ) * (L + 1 : ℝ) * D := by
    calc
      _ = ∑ a : Fin s × Fin (L + 1), ((sourceValues x (L + 1) a).divisors.card : ℝ) := by norm_cast
      _ ≤ ∑ _a : Fin s × Fin (L + 1), D := sum_le_sum (fun a _ ↦ hdiv a)
      _ = _ := by simp [Fintype.card_prod, Nat.cast_mul]
  have hbase := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ L + 1)
  calc
    _ ≤ (((L + 1) * ∑ a : Fin s × Fin (L + 1), (sourceValues x (L + 1) a).divisors.card : ℕ) : ℝ) ^ k := by
      exact_mod_cast card_targets_le (sourceValues x (L + 1)) (L + 1) k N N hN
    _ = (↑(L + 1) * ((∑ a : Fin s × Fin (L + 1), (sourceValues x (L + 1) a).divisors.card : ℕ) : ℝ)) ^ k := by norm_cast
    _ ≤ ((L + 1 : ℝ) * ((s : ℝ) * (L + 1 : ℝ) * D)) ^ k := by
      apply pow_le_pow_left₀ (by positivity)
      simpa only [Nat.cast_add, Nat.cast_one] using hbase
    _ = _ := by simp only [mul_pow, pow_mul, pow_two]; ring

end PaperP1.FixedSourceCertificate
