import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring

open Nat

lemma even_ind {p : ℕ → Prop} (h₀ : p 0) (hind : ∀ n, p n → p (n + 2)) : ∀ n, p (2 * n) := by
  intro n
  induction' n with n hn
  · simp
    exact h₀
  · have temp : p (2 * n + 2) := hind (2 * n) hn
    have : 2 * n + 2 = 2 * (n + 1) := by ring
    rw [this] at temp
    exact temp

lemma odd_ind {p : ℕ → Prop} (h₀ : p 1) (hind : ∀ n, p n → p (n + 2)) : ∀ n, p (2 * n + 1) := by
  intro n
  induction' n with n hn
  · simp
    exact h₀
  · have temp : p (2 * n + 3) := hind (2 * n + 1) hn
    have : 2 * n + 3 = 2 * (n + 1) + 1 := by ring
    rw [this] at temp
    exact temp

theorem odd_even_ind {p : ℕ → Prop} (h₀ : p 0) (h₁ : p 1) (hind : ∀ m, p m → p (m + 2)) : ∀ m, p m := by
  intro m
  rcases Nat.even_or_odd m with hm | hm
  · rw [even_iff_exists_two_mul] at hm
    rcases hm with ⟨b, rfl⟩
    exact even_ind h₀ hind b
  · rw [odd_iff_exists_bit1] at hm
    rcases hm with ⟨b, rfl⟩
    exact odd_ind h₁ hind b

theorem spiral_ind {p q : ℕ → Prop} (hp : p 0) (hq : q 0) (hpqind : ∀ m, p m → q (m + 1)) (hqpind : ∀ m, q m → p (m + 1)) : (∀ m, p m) ∧ (∀ m, q m) := by
  constructor
  · intro m
    induction' m using odd_even_ind with m hm
    . exact hp
    . exact hqpind 0 hq
    . exact hqpind (m + 1) (hpqind m hm)
  · have hq1 : q 1 := hpqind 0 hp
    have hqm2 : ∀ m, q m → q (m + 2) := by
      intro m hm
      exact hpqind (m + 1) (hqpind m hm)
    exact odd_even_ind hq hq1 hqm2

theorem double_ind {p : ℕ → ℕ → Prop} (hm : ∀ m, p m 0) (hn : ∀ n, p 0 n)
    (hind : ∀ m n, p (m + 1) n → p m (n + 1) → p (m + 1) (n + 1)) : ∀ m n, p m n := by
  intro m
  induction' m with m hdm
  · exact hn
  · intro n
    induction' n with n hdn
    · apply hm
    · apply hind m n hdn (hdm (n + 1))

theorem double_ind' {p : ℕ → ℕ → Prop} (hm : ∀ m, p m 0) (hn : ∀ n, p 0 n)
    (hind : ∀ m n, p (m + 1) n → p m (n + 1) → p (m + 1) (n + 1)) : ∀ m n, p m n := by
  refine Nat.rec ?_ ?_
  · exact hn
  · intro n hdn
    refine Nat.rec ?_ ?_
    · apply hm
    · intro n₁ hn₁
      apply hind n n₁ hn₁ (hdn n₁.succ)

theorem double_ind'' {p : ℕ → ℕ → Prop} (hm : ∀ m, p m 0) (hn : ∀ n, p 0 n)
    (hind : ∀ m n, p (m + 1) n → p m (n + 1) → p (m + 1) (n + 1)) : ∀ m n, p m n := by
  refine Nat.rec ?_ (fun m hdm ↦ ?_)
  · exact hn
  · refine Nat.rec ?_ (fun n hdn ↦ ?_)
    · apply hm
    · apply hind m n hdn (hdm (n + 1))
