import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic

open Finset

-- ADA University Olympiad, Problem 2 (Y. Aliyev)
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime k

noncomputable def primeProd (n : ℕ) : ℕ := ∏ i ∈ Finset.range n, pr i

theorem infPrime : (Set.ofPred Nat.Prime).Infinite := by
  simpa [Set.ofPred, Set.Infinite] using Nat.infinite_setOf_prime

theorem primeProd_pos (n : ℕ) : 0 < primeProd n := by
  apply Finset.prod_pos
  intro i _
  exact (Nat.nth_mem_of_infinite infPrime i).pos

theorem prime_lt_pn_eq_pk {n q : ℕ} (hq : Nat.Prime q) (hlt : q < pr n) :
    ∃ k < n, q = pr k := by
  set k := Nat.count Nat.Prime q with hkdef
  have hk_eq : pr k = q := Nat.nth_count hq
  have hlt' : pr k < pr n := by rw [hk_eq]; exact hlt
  have hkn : k < n := (Nat.nth_lt_nth infPrime).mp hlt'
  exact ⟨k, hkn, hk_eq.symm⟩

theorem ada_prime_gap_upper (n : ℕ) (hn : n ≥ 1) :
    pr n ≤ primeProd n + 1 := by
  set N := primeProd n + 1 with hN
  have hNpos : N > 0 := by omega
  have hN1 : N ≠ 1 := by have := primeProd_pos n; omega
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hN1
  by_contra hcon
  push_neg at hcon
  have hqleN : q ≤ N := Nat.le_of_dvd hNpos hqdvd
  have hqltpn : q < pr n := lt_of_le_of_lt hqleN hcon
  obtain ⟨k, hk, hqk⟩ := prime_lt_pn_eq_pk hq hqltpn
  have hqdvdprod : q ∣ primeProd n := by
    rw [hqk]; exact Finset.dvd_prod_of_mem pr (Finset.mem_range.mpr hk)
  have hone : q ∣ (1:ℕ) := by
    have h1 : (q:ℤ) ∣ (N:ℤ) := Int.natCast_dvd_natCast.mpr hqdvd
    have h2 : (q:ℤ) ∣ (primeProd n : ℤ) := Int.natCast_dvd_natCast.mpr hqdvdprod
    have heq : (N:ℤ) - (primeProd n : ℤ) = 1 := by rw [hN]; push_cast; ring
    have hz : (q:ℤ) ∣ (1:ℤ) := heq ▸ dvd_sub h1 h2
    exact_mod_cast hz
  exact hq.ne_one (Nat.dvd_one.mp hone)

theorem ada_prime_gap_lower (n : ℕ) (hn : n ≥ 2) :
    pr n ≤ primeProd n - 1 := by
  have hp0dvd : pr 0 ∣ primeProd n := Finset.dvd_prod_of_mem pr (Finset.mem_range.mpr (by omega))
  have hp0prime : Nat.Prime (pr 0) := Nat.nth_mem_of_infinite infPrime 0
  have hp0ge2 : pr 0 ≥ 2 := hp0prime.two_le
  have hpos := primeProd_pos n
  have hge2 : primeProd n ≥ 2 := by
    have h1 := Nat.le_of_dvd hpos hp0dvd
    omega
  have hp1dvd : pr 1 ∣ primeProd n := Finset.dvd_prod_of_mem pr (Finset.mem_range.mpr (by omega))
  have hp1prime : Nat.Prime (pr 1) := Nat.nth_mem_of_infinite infPrime 1
  have hp0lt1 : pr 0 < pr 1 := (Nat.nth_lt_nth infPrime).mpr (by omega)
  have hne2 : primeProd n ≠ 2 := by
    intro heq2
    have h3 := Nat.le_of_dvd (by omega) hp1dvd
    have h4 := hp1prime.two_le
    omega
  set N := primeProd n - 1 with hN
  have hNpos : N > 0 := by omega
  have hN1 : N ≠ 1 := by omega
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hN1
  by_contra hcon
  push_neg at hcon
  have hqleN : q ≤ N := Nat.le_of_dvd hNpos hqdvd
  have hqltpn : q < pr n := lt_of_le_of_lt hqleN hcon
  obtain ⟨k, hk, hqk⟩ := prime_lt_pn_eq_pk hq hqltpn
  have hqdvdprod : q ∣ primeProd n := by
    rw [hqk]; exact Finset.dvd_prod_of_mem pr (Finset.mem_range.mpr hk)
  have hone : q ∣ (1:ℕ) := by
    have h1 : (q:ℤ) ∣ (N:ℤ) := Int.natCast_dvd_natCast.mpr hqdvd
    have h2 : (q:ℤ) ∣ (primeProd n : ℤ) := Int.natCast_dvd_natCast.mpr hqdvdprod
    have heq : (primeProd n : ℤ) - (N:ℤ) = 1 := by
      have hcast : (N:ℤ) = (primeProd n : ℤ) - 1 := by
        rw [hN]; exact Nat.cast_sub (by omega : 1 ≤ primeProd n)
      rw [hcast]; ring
    have hz : (q:ℤ) ∣ (1:ℤ) := heq ▸ dvd_sub h2 h1
    exact_mod_cast hz
  exact hq.ne_one (Nat.dvd_one.mp hone)
