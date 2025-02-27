open Nat

namespace VariousInduction

lemma even_ind (p : ℕ → Prop) (h₀ : p 0) (hind : ∀ n, p n → p (n + 2)) : ∀ n, p (2 * n) := by
  intro n
  induction' n with n hn
  · simp
    exact h₀
  · have temp : p (2 * n + 2) := hind (2 * n) hn
    have : 2 * n + 2 = 2 * (n + 1) := by ring
    rw [this] at temp
    exact temp

lemma odd_ind (p : ℕ → Prop) (h₀ : p 1) (hind : ∀ n, p n → p (n + 2)) : ∀ n, p (2 * n + 1) := by
  intro n
  induction' n with n hn
  · simp
    exact h₀
  · have temp : p (2 * n + 3) := hind (2 * n + 1) hn
    have : 2 * n + 3 = 2 * (n + 1) + 1 := by ring
    rw [this] at temp
    exact temp

theorem odd_even_ind (p : ℕ → Prop) (h₀ : p 0) (h₁ : p 1) (hind : ∀ m, p m → p (m + 2)) : ∀ m, p m := by
  intro m
  rcases Nat.even_or_odd m with hm | hm
  · rw [even_iff_exists_two_mul] at hm
    rcases hm with ⟨b, rfl⟩
    exact even_ind p h₀ hind b
  · rw [odd_iff_exists_bit1] at hm
    rcases hm with ⟨b, rfl⟩
    exact odd_ind p h₁ hind b

theorem spiral_ind (p q : ℕ → Prop) (hp : p 0) (hq : q 0) (hpqind : ∀ m, p m → q (m + 1)) (hqpind : ∀ m, q m → p (m + 1)) : (∀ m, p m) ∧ (∀ m, q m) := by
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
    exact odd_even_ind q hq hq1 hqm2

end VariousInduction
