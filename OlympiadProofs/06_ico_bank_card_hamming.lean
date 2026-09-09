import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

open Finset

theorem bank_card_bound (S : Finset (Fin 12 → Fin 10))
    (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 2 ≤ hammingDist x y) :
    S.card ≤ 10 ^ 11 := by
  let f : (Fin 12 → Fin 10) → (Fin 11 → Fin 10) := fun x i => x i.castSucc
  have hinj : Set.InjOn f S := by
    intro x hx y hy hxy
    by_contra hne
    have h2 := hS x hx y hy hne
    have hagree : ∀ i : Fin 12, i.val ≠ 11 → x i = y i := by
      intro i hi
      have hlt : i.val < 11 := by have := i.isLt; omega
      have heq := congrFun hxy ⟨i.val, hlt⟩
      have hcast : (⟨i.val, hlt⟩ : Fin 11).castSucc = i := by
        apply Fin.ext; simp
      simpa [f, hcast] using heq
    have hsub : Finset.filter (fun i => x i ≠ y i) Finset.univ ⊆
        ({(⟨11, by omega⟩ : Fin 12)} : Finset (Fin 12)) := by
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_singleton]
      by_contra hi11
      apply hi.2
      apply hagree
      intro hval
      apply hi11
      apply Fin.ext
      simpa using hval
    have hle1 : hammingDist x y ≤ 1 := by
      have hc := Finset.card_le_card hsub
      simpa [hammingDist] using hc
    omega
  calc S.card = (S.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card (Fin 11 → Fin 10) := Finset.card_le_univ _
    _ = 10 ^ 11 := by simp
