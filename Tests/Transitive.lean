import Autograde.RecordDeclsElab
import Autograde.Grade

stop_recording

@[grade (config := { points := 2 })]
theorem ex1 (n m : Nat) : n + m = m + n := by
  omega

@[grade (config := { points := 2, allowedPrerequisites := #[``ex1] })]
theorem ex2 (n m k l : Nat) : n + m + k + l = m + n + l + k := by
  rw [ex1 n m, Nat.add_assoc, ex1 k l, ← Nat.add_assoc]

-- silent sorry
axiom ssorry : False

resume_recording

namespace Test1

/- Here `sol2` should be counted as a full solution to `ex2`, although it uses the forbidden
`ssorry` axiom, since the latter is only used via `sol1`, which is an allowed prerequisite for
`ex2`. -/

theorem auxLemma : False := ssorry

theorem sol1 (n m : Nat) : n + m = m + n :=
  auxLemma.elim

theorem sol2 (n m k l : Nat) : n + m + k + l = m + n + l + k := by
  rw [sol1 n m, Nat.add_assoc, sol1 k l, ← Nat.add_assoc]

/--
info: ex1: Partial solutions: [(Test1.sol1, #[(ssorry, [Test1.auxLemma, Test1.sol1])])] => 1.000000 / 2.000000
ex2: Success: Solved by Test1.sol2. => 2.000000 / 2.000000
total: 3.000000 / 4.000000
-/
#guard_msgs in
#grade

end Test1

clear_decls

namespace Test2

/- Here `sol2` should not be counted as a full solution, since it also directly uses `intLemma`, which
depends on `ssorry`. -/

theorem sol1 (n m : Nat) : n + m = m + n :=
  ssorry.elim

theorem intLemma (n m : Nat) : n = m := by
  rw [← Nat.add_one_inj, sol1 n 1]
  exact ssorry.elim

theorem sol2 (n m k l : Nat) : n + m + k + l = m + n + l + k := by
  rw [intLemma n m, Nat.add_assoc, sol1 k l, ← Nat.add_assoc]

/--
info: ex1: Partial solutions: [(Test2.sol1, #[(ssorry, [Test2.sol1])])] => 1.000000 / 2.000000
ex2: Partial solutions: [(Test2.sol2, #[(ssorry, [Test2.intLemma, Test2.sol2])])] => 1.000000 / 2.000000
total: 2.000000 / 4.000000
-/
#guard_msgs in
#grade

end Test2

clear_decls
