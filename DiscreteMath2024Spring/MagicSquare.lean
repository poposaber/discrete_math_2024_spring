import Mathlib.Data.PNat.Notation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Nat
open BigOperators

lemma sub_fin_lt (n : ℕ+) (m : ℕ) : n - 1 - m < n := by
  calc n - 1 - m
  _ ≤ n - 1 := Nat.sub_le (n - 1) m
  _ < n := Nat.sub_one_lt (Nat.ne_of_gt n.2)

lemma sub_left_eq {k m n : ℕ} (h₁ : k - m = k - n) (h₂ : m ≤ k) (h₃ : n ≤ k) : m = n := by
  have : k - m + m = k - n + n := Eq.trans (Nat.sub_add_cancel h₂) (Nat.sub_add_cancel h₃).symm
  rw [h₁] at this
  apply Nat.add_left_cancel this

lemma sum_sub' {n : ℕ+} {f : Fin n → ℕ} {a : ℕ} (h : ∀ m, f m ≤ a) : ∑ x, (a - f x) = (∑ (x : Fin n), a) - ∑ x, f x := by
  have : ∑ x, f x ≤ (∑ (_ : Fin n), a) := by
    apply sum_le_sum
    intro i _
    exact h i
  symm
  rw [Nat.sub_eq_iff_eq_add this]
  rw [← sum_add_distrib]
  congr
  ext x
  exact (Nat.sub_eq_iff_eq_add (h x)).mp rfl



structure MagicSquare (n : ℕ+) where
  toFun : Fin n → Fin n → ℕ
  in_square : ∀ i j, 1 ≤ toFun i j ∧ toFun i j ≤ n ^ 2
  inj : ∀ i₁ j₁ i₂ j₂, toFun i₁ j₁ = toFun i₂ j₂ → i₁ = i₂ ∧ j₁ = j₂
  sum_eq : ∃ s, (∀ i, ∑ k, toFun i k = s) ∧ (∀ i, ∑ k, toFun k i = s) ∧ ∑ k, toFun k k = s ∧ ∑ k, toFun k ⟨n - 1 - k, sub_fin_lt n k⟩ = s

instance {n : ℕ+} : CoeFun (MagicSquare n) (fun _ ↦ Fin n → Fin n → ℕ) where
  coe := MagicSquare.toFun

attribute [coe] MagicSquare.toFun

section
variable (n : ℕ+) (A : MagicSquare n)
example : MagicSquare n where
  toFun i j := n ^ 2 + 1 - A i j
  in_square i j := by
    constructor <;> simp
    · calc 1
        _ = (n : ℕ) ^ 2 + 1 - n ^ 2 := by simp
        _ ≤ (n : ℕ) ^ 2 + 1 - A i j := by apply Nat.sub_le_sub_left (A.in_square i j).2
    · apply (A.in_square i j).1
  inj i₁ j₁ i₂ j₂ := by
    simp
    intro h
    have le1 : ∀ i j,  A i j ≤ (n : ℕ) ^ 2 + 1 := by
      intro i j
      calc A i j
      _ ≤ (n : ℕ) ^ 2 := (A.in_square i j).2
      _ ≤ (n : ℕ) ^ 2 + 1 := by exact Nat.le_add_right (n ^ 2) 1
    have : A i₁ j₁ = A i₂ j₂ := sub_left_eq h (le1 i₁ j₁) (le1 i₂ j₂)
    apply A.inj i₁ j₁ i₂ j₂ this
  sum_eq := by
    simp
    rcases A.sum_eq with ⟨s, hs₁, hs₂, hs₃, hs₄⟩
    use n * (n ^ 2 + 1) - s
    have le1 : ∀ i j,  A i j ≤ (n : ℕ) ^ 2 + 1 := by
      intro i j
      calc A i j
      _ ≤ (n : ℕ) ^ 2 := (A.in_square i j).2
      _ ≤ (n : ℕ) ^ 2 + 1 := by exact Nat.le_add_right (n ^ 2) 1
    constructor
    · intro i
      rw [sum_sub' (le1 i), hs₁ i, sum_const, Finset.card_univ, Fintype.card_fin n]
      rfl
    constructor
    · intro i
      rw [sum_sub', hs₂ i, sum_const, Finset.card_univ, Fintype.card_fin n]
      rfl
      intro m
      exact le1 m i
    constructor
    · rw [sum_sub', hs₃, sum_const, Finset.card_univ, Fintype.card_fin n]
      rfl
      intro m
      exact le1 m m
    · rw [sum_sub', hs₄, sum_const, Finset.card_univ, Fintype.card_fin n]
      rfl
      intro m
      apply le1 m
end
