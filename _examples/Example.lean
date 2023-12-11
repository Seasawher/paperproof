-- This is the example we always use in demos&videos
import Mathlib.Data.Set.Basic
import Paperproof

theorem blue (s t : Set Nat) : s ∩ t = t ∩ s := by
  ext x
  apply Iff.intro

  intro h1
  rw [Set.mem_inter_iff, and_comm] at h1
  exact h1

  intro h2
  rw [Set.mem_inter_iff, and_comm] at h2
  exact h2

-- We didn't make this render nicely, but I started thinking this might be an artificial example.
example (a b c d e f : ℕ) (h1 : b = e) (h2 : e = d): (a = b) → (b = c) → (e = f) → True := by
  intros ab cd ef
  rw [h1, h2] at *
  trivial

-- Example with a grid any multi-out goals
example (p q r s : Prop) (h : q = s) : p ∧ q → r ∧ s → true := by
  -- intros hpq
  -- cases' hpq with hp hq
  -- rewrite [h] at hq
  -- intros hrs
  -- cases' hrs with hr hs
  -- trivial

  intro hpq hrs
  cases' hpq with hp hq
  rewrite [h] at hq
  cases' hrs with hr hs

example (p q r s : Prop) : p ∧ q → r ∧ s → true := by
  intros hpq hrs
  cases' hpq with hp hq
  cases' hrs with hr hs
  trivial

-- this is for arrows
example (a b c d e f : ℕ) (h : b = e) (h₂ : e = d): (a = b) → (b = c) → (e = f) → True := by
  intros ab cd ef
  rw [h, h₂] at *
  trivial

-- this is for arrows
example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m ≤ 6 := by
  have h3 := calc
      m + 3 ≤ 2 * n - 1 := by gcongr
      _ ≤ 2 * 5 - 1 := by gcongr
      _ = 9 := by norm_num
  clear h1 h2
  linarith
