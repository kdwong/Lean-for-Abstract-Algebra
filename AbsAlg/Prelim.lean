import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Find

open Int Set

-- Division Algorithm
theorem division_algorithm (a b : ℤ) (hb : b > 0) :
  ∃! p : ℤ × ℤ, let (q, r) := p; (a = b * q + r) ∧ (0 ≤ r) ∧ (r < b) := by
  -- 1. Existence
  use (a / b, a % b)
  dsimp
  constructor
  · constructor
    · exact (Int.mul_ediv_add_emod a b).symm
    · constructor
      · exact Int.emod_nonneg a (ne_of_gt hb)
      · exact Int.emod_lt_of_pos a hb
  -- 2. Uniqueness
  · rintro ⟨q', r'⟩ ⟨h_eq, h_nonneg, h_lt⟩
    dsimp at h_eq
    have hq : q' = a / b := by
      rw [h_eq, add_comm, mul_comm]
      rw [Int.add_mul_ediv_right r' q' (ne_of_gt hb)]
      rw [Int.ediv_eq_zero_of_lt h_nonneg h_lt]
      simp
    have hr : r' = a % b := by
      rw [h_eq, add_comm, mul_comm]
      rw [Int.add_mul_emod_self_right r' q' b]
      rw [Int.emod_eq_of_lt h_nonneg h_lt]
    apply Prod.ext
    · exact hq
    · exact hr

-- Euclidean Algorithm
def euclid_alg (x y : ℤ) : ℤ :=
  if h : y = 0 then
    x.natAbs
  else
    euclid_alg y (x % y)
termination_by y.natAbs
decreasing_by
rw [ ← Int.ofNat_lt, Int.natAbs_of_nonneg ( Int.emod_nonneg _ h ) ]
exact Int.emod_lt _ h

#eval euclid_alg 18 123


-- Bézout's Theorem
theorem bezout_int (x y : ℤ) : ∃ a b : ℤ, a * x + b * y = Int.gcd x y := by
  exact Int.gcd_eq_gcd_ab x y ▸ ⟨ Int.gcdA x y, Int.gcdB x y, by ring ⟩

/-
Below is a function that computes the Bezout coefficients for two
integers x and y using the extended Euclidean algorithm.
Returns a pair (a, b) such that ax + by = gcd(x, y).
Note that (x / y) = q, where  x = qy + r   in the division algorithm.
-/
def bezout_coeffs (x y : ℤ) : ℤ × ℤ :=
  if h : y = 0 then
    (x.sign, 0)
  else
    let (a', b') := bezout_coeffs y (x % y)
    (b', a' - b' * (x / y))
termination_by y.natAbs
decreasing_by
rw [ ← Int.ofNat_lt, Int.natAbs_of_nonneg ( Int.emod_nonneg _ h ) ]
exact Int.emod_lt _ h


theorem bezout_coeffs_correct (x y : ℤ) : let (a, b) := bezout_coeffs x y
  a * x + b * y = Int.gcd x y := by
  unfold bezout_coeffs
  by_cases hy : y = 0
  · simp [hy]
  · simp only [hy]
    have ih := bezout_coeffs_correct y (x % y)
    cases h : bezout_coeffs y (x % y) with
    | mk a' b' =>
      simp only [h] at ih
      have hxy : Int.gcd y (x % y) = Int.gcd x y := by
        conv_lhs => rw [Int.gcd_comm]
        conv_rhs => rw [Int.gcd_comm]
        nth_rw 2 [Int.gcd_comm]
        exact Int.gcd_emod x y
      calc b' * x + (a' - b' * (x / y)) * y
          = b' * x + a' * y - b' * (x / y) * y := by ring
        _ = b' * x + a' * y - b' * y * (x / y) := by ring
        _ = a' * y + b' * (x - y * (x / y)) := by ring
        _ = a' * y + b' * (x % y) := by rw [Int.emod_def]
        _ = Int.gcd y (x % y) := ih
        _ = Int.gcd x y := by rw [hxy]
termination_by y.natAbs
decreasing_by
  rw [← Int.ofNat_lt, Int.natAbs_of_nonneg (Int.emod_nonneg _ hy)]
  exact Int.emod_lt _ hy

/-
Bezout's identity for integers, proven using the manually defined Euclidean algorithm.
-/
theorem bezout_int_manual (x y : ℤ) : ∃ a b : ℤ, a * x + b * y = Int.gcd x y := by
  exact ⟨ _, _, bezout_coeffs_correct x y ⟩
