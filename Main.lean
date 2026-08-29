import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


def main : IO Unit :=
  IO.println "Hello, Lean 4!"

-- Example: Simple theorem proving (commutativity of addition)
theorem add_comm_example (a b : Nat) : a + b = b + a := by
  omega

-- Example: A proof with explicit induction
theorem add_comm_induction (a b : Nat) : a + b = b + a := by
  induction a with
  | zero =>
    rw [Nat.zero_add, Nat.add_zero]
  | succ n ih =>
    rw [Nat.succ_add, Nat.add_succ, ih]

-- Ex3 from https://zenn.dev/jun1013/articles/a491b2f42afe0a
example (a b: Real):
  (a + b)^2  = a^2 + 2 * a * b + b^2 := by
  ring

-- Ex 4
example (x : Real): x^2 - 6*x + 9 >= 0 := by
  nlinarith [sq_nonneg (x - 3)]

#check add_comm_example
#eval main
#eval 2+4
