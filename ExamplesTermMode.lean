import Lean
import Paperproof

theorem branch (P Q U : Prop) (p : P) :
  ((q : Q) → P ∧ Q) ∧ ((u : U) → U ∧ P) :=
  And.intro (fun q => ⟨p, q⟩) (fun u => ⟨u, p⟩)

theorem prod (P Q : Prop) (p1 : P) (q1 : Q) :
     (p2 : P) → (q2 : Q) → (P ∧ Q) ∧ (Q ∧ P)  :=
  fun p2 => fun q2 => And.intro ⟨p1, q1⟩ ⟨q2, p2⟩

theorem tactic_prod (A B : Prop) (a : A) (b : B) : A ∧ B := by
  exact ⟨a, b⟩
