import LeanSearchClient
import Mathlib.Tactic.Linarith

namespace Exercises01

def student_name : String := sorry

-- From the lecture.
def maximum (n m : Nat) : Nat := if n ≤ m then m else n

-- Exercise 1: 1 point
theorem and_commutes {P Q : Prop} : P ∧ Q → Q ∧ P := by sorry

-- Exercise 2: 1 point
theorem or_commutes {P Q : Prop} : P ∨ Q → Q ∨ P := by sorry

-- Exercise 3: 1 point
theorem implication_transitive {P Q R : Prop} : (P → Q) → (Q → R) → (P → R) := by sorry

-- Exercise 4: 1 point
theorem forall_conjunction {P R : Nat → Prop} : (∀ n, P n ∧ R n) → (∀ n, P n) := by sorry


-- Exercise 5: 2 points
theorem maximum_associative (n m k : Nat) :
  maximum n (maximum m k) = maximum (maximum n m) k := by sorry


-- Define the following function.
--
-- `clamp lowerbound upperbound value` should:
-- - return `k` if it is within the bounds,
-- - return `lowerbound` if `k` is below `lowerbound`
-- - return `upperbound` if `k` is above `upperbound`
--
-- If `lowerbound > upperbound`, you may return any value.
--
-- You may use the standard library functions `Nat.min` and `Nat.max`
-- and associated theorems, or reason about `≤` as we did before.
def clamp (lb ub k : Nat) : Nat := sorry

-- Exercise 6: 2 points
theorem clamp_within_bounds_is_identity (lb ub k : Nat) :
  lb ≤ k → k ≤ ub → clamp lb ub k = k := by sorry

-- Exercise 7: 2 points
theorem clamp_below_lower_bound_is_lower_bound (lb ub k : Nat) :
  k ≤ lb → lb ≤ ub → clamp lb ub k = lb := by sorry

-- Exercise 8: 2 points
theorem clamp_above_upper_bound_is_upper_bound (lb ub k : Nat) :
  ub ≤ k → lb ≤ ub → clamp lb ub k = ub := by sorry

end Exercises01
