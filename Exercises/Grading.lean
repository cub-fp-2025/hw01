import Exercises.Autograder
import Exercises.Problems

open Exercises01

def ex1 {P Q : Prop} : P ∧ Q → Q ∧ P := and_commutes
def ex2 {P Q : Prop} : P ∨ Q → Q ∨ P := or_commutes
def ex3 {P Q R : Prop} : (P → Q) → (Q → R) → (→ R) :=  implication_transitive
def ex4 {P R : Nat → Prop} : (∀ n, P n ∧ R n) → (∀ n, P n) :=  forall_conjunction
def ex5 (n m k : Nat) : maximum n (maximum m k) = maximum (maximum n m) k :=  maximum_associative
def ex6 (lb ub k : Nat) : lb ≤ k → k ≤ ub → clamp lb ub k = k :=  clamp_within_bounds_is_identity
def ex7 (lb ub k : Nat) : k ≤ lb → lb ≤ ub → clamp lb ub k = lb :=  clamp_below_lower_bound_is_lower_bound
def ex8 (lb ub k : Nat) : ub ≤ k → lb ≤ ub → clamp lb ub k = ub :=  clamp_above_upper_bound_is_upper_bound

#eval student_name

#print_grade_results ex1 ex2 ex3 ex4 ex5 ex6 ex7 ex8 ex9
