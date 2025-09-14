import LeanSearchClient
import Mathlib.Tactic.Linarith

namespace Exercises01

def student_name : String := "Model solution"

-- From the lecture.
def maximum (n m : Nat) : Nat := if n ≤ m then m else n

-- Exercise 1: 1 point
theorem and_commutes {P Q : Prop} : P ∧ Q → Q ∧ P := fun ⟨ p, q ⟩ => ⟨ q, p ⟩
example {P Q : Prop} : P ∧ Q → Q ∧ P := by
  intro H
  cases H
  constructor
  · assumption
  · assumption
  -- alternatively: repeat assumption

-- Exercise 2: 1 point
theorem or_commutes {P Q : Prop} : P ∨ Q → Q ∨ P
  | Or.inl p => Or.inr p
  | Or.inr q => Or.inl q
example {P Q : Prop} : P ∨ Q → Q ∨ P := by
  intro H
  cases H with
  | inl p =>
      right
      assumption
  | inr q =>
      left
      assumption


-- Exercise 3: 1 point
theorem implication_transitive {P Q R : Prop} : (P → Q) → (Q → R) → (P → R) := fun pq qr p => qr (pq p)
example {P Q R : Prop} : (P → Q) → (Q → R) → (P → R) := by
  intro pq qr p
  apply qr
  apply pq
  assumption
example {P Q R : Prop} : (P → Q) → (Q → R) → (P → R) := by
  intro pq qr p
  have q := pq p
  have r := qr q
  exact r

-- Exercise 4: 1 point
theorem forall_conjunction {P R : Nat → Prop} : (∀ n, P n ∧ R n) → (∀ n, P n) := fun H n => (H n).1
example {P R : Nat → Prop} : (∀ n, P n ∧ R n) → (∀ n, P n) := by
  intros H n
  cases (H n)
  assumption

-- Exercise 5: 2 points
theorem maximum_associative (n m k : Nat) : maximum n (maximum m k) = maximum (maximum n m) k := by
  simp [maximum]
  split
  · split
    · split <;> rfl
    · split
      · linarith
      · rfl
  · split
    · rfl
    · split
      · linarith
      · rfl

-- A more concise approach.
example (n m k : Nat) : maximum n (maximum m k) = maximum (maximum n m) k := by
  simp [maximum]
  -- repeat continues applying a tactic until it fails
  -- first tries all the listed tactics and succeeds if any succeeds
  repeat (first | split | rfl | linarith)


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
def clamp (lb ub k : Nat) : Nat :=
  if k ≤ lb then lb
  else if k ≥ ub then ub
  else k

-- Exercise 6: 2 points
theorem clamp_within_bounds_is_identity (lb ub k : Nat) : lb ≤ k → k ≤ ub → clamp lb ub k = k := by
  intro lb_k k_ub
  simp [clamp]
  split
  · linarith
  · split
    · linarith
    · rfl

-- Exercise 7: 2 points
-- You can do it in the same style as the above, but...
theorem clamp_below_lower_bound_is_lower_bound (lb ub k : Nat) : k ≤ lb → lb ≤ ub → clamp lb ub k = lb := by
  intro lb_k lb_ub
  simp [clamp]
  -- notice that `simp` already handles one if case for us
  -- if this is too big a step, use `rw [clamp]` or `unfold clamp` instead
  intro lb_k
  split <;> linarith

-- Exercise 8: 2 points
theorem clamp_above_upper_bound_is_upper_bound (lb ub k : Nat) : ub ≤ k → lb ≤ ub → clamp lb ub k = ub := by
  intro ub_k lb_ub
  simp [clamp]
  split
  · linarith
  · rfl -- the split used the ub_k conclusion

-- Solution for if you used the standard library
def clamp_stdlib (lb ub k : Nat) : Nat := (k.max lb).min ub

example (lb ub k : Nat) : lb ≤ k → k ≤ ub → clamp_stdlib lb ub k = k := by
  intro lb_k k_ub
  simp [clamp_stdlib]
  have : k.max lb = k := by
    apply Nat.max_eq_left
    assumption
  rw [this]
  have : k.min ub = k := by
    apply Nat.min_eq_left
    assumption
  rw [this]

example (lb ub k : Nat) : k ≤ lb → lb ≤ ub → clamp_stdlib lb ub k = lb := by
  intro lb_k lb_ub
  simp [clamp_stdlib]
  have : k.max lb = lb := by
    apply Nat.max_eq_right
    assumption
  rw [this]
  have : lb.min ub = lb := by
    apply Nat.min_eq_left
    assumption
  rw [this]

example (lb ub k : Nat) : ub ≤ k → lb ≤ ub → clamp_stdlib lb ub k = ub := by
  intro ub_k lb_ub
  rw [clamp_stdlib]
  have : k.max lb = k := by
    apply Nat.max_eq_left
    linarith
  rw [this]
  have : k.min ub = ub := by
    apply Nat.min_eq_right
    assumption
  rw [this]

example (lb ub k : Nat) : ub ≤ k → lb ≤ ub → clamp_stdlib lb ub k = ub := by
  intro ub_k lb_ub
  simp [clamp_stdlib] -- behold the power of simp
  left
  assumption

end Exercises01
