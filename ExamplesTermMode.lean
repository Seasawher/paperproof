import Lean
import Paperproof

theorem prod (P Q : Prop) (p1 p2 : P) (q1 : Q) :
     (q2 : Q) → (P ∧ Q) ∧ (Q ∧ P)  :=
  fun q2 => And.intro ⟨p1, q1⟩ ⟨q2, p2⟩

theorem tactic_prod (A B : Prop) (a : A) (b : B) : A ∧ B := by
  exact ⟨a, b⟩
