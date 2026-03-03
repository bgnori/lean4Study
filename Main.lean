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

#check add_comm_example
#eval main
