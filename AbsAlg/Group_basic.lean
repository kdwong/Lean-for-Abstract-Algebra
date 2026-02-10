import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic


class MyGroup (G : Type) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul   : ∀ a : G, mul one a = a
  mul_one   : ∀ a : G, mul a one = a
  mul_left_inv : ∀ a : G, mul (inv a) a = one
  mul_right_inv : ∀ a : G, mul a (inv a) = one

infixl:70 " * " => MyGroup.mul
notation "e" => MyGroup.one
postfix:100 "⁻¹" => MyGroup.inv


class MyAddGroup (G : Type) where
  add : G → G → G
  zero : G
  neg : G → G
  add_assoc : ∀ a b c : G, add (add a b) c = add a (add b c)
  add_comm : ∀ a b : G, add a b = add b a
  zero_add : ∀ a : G, add zero a = a
  add_left_neg : ∀ a : G, add (neg a) a = zero


notation "o" => MyAddGroup.zero
postfix:100 "⁻" => MyAddGroup.neg


class MyAbelianGroup (G : Type) extends MyGroup G where
  mul_comm : ∀ a b : G, a * b = b * a


instance [i : MyAddGroup G] : MyAbelianGroup G where
  mul := i.add
  one := i.zero
  inv := i.neg
  mul_assoc := i.add_assoc
  one_mul := i.zero_add
  mul_one := fun a => by
    rw [i.add_comm]
    exact i.zero_add a
  mul_left_inv := i.add_left_neg
  mul_right_inv := fun a => by
    rw [i.add_comm]
    exact i.add_left_neg a
  mul_comm := i.add_comm

variable {G : Type} [MyGroup G]

-- 1. Uniqueness of Identity
lemma MyGroup.unique_identity (e' : G) (h : ∀ a, e' * a = a) : e' = e := by
  calc e' = e' * e := by rw [MyGroup.mul_one]
       _  = e      := by rw [h]


-- 2. Uniqueness of Inverses
lemma MyGroup.left_inv_unique (x y : G) (h : y * x = e) : y = x⁻¹ := by
  calc y = y * e := by rw [MyGroup.mul_one]
       _ = y * (x * x⁻¹) := by rw [MyGroup.mul_right_inv]
       _ = (y * x) * x⁻¹ := by rw [← MyGroup.mul_assoc]
       _ = e * x⁻¹ := by rw [h]
       _ = x⁻¹ := by rw [MyGroup.one_mul]


theorem MyGroup.right_inv_unique (a b : G) (h : a * b = e) : b = a⁻¹ := by
  calc b = e * b       := by rw [MyGroup.one_mul]
       _ = (a⁻¹ * a) * b := by rw [MyGroup.mul_left_inv]
       _ = a⁻¹ * (a * b) := by rw [MyGroup.mul_assoc]
       _ = a⁻¹ * e     := by rw [h]
       _ = a⁻¹         := by rw [MyGroup.mul_one]


-- 3. Some other standard theorems
lemma MyGroup.inv_one : (e : G)⁻¹ = e := by
  have h : (e : G) * e = e := by rw [MyGroup.mul_one]
  exact (left_inv_unique e e h).symm

lemma MyGroup.inv_inv (g : G) : (g⁻¹)⁻¹ = g := by
  have h : g * (g⁻¹) = e := by rw [MyGroup.mul_right_inv]
  exact (left_inv_unique (g⁻¹) g h).symm

lemma MyGroup.mul_inv_reverse {a b : G} : (a*b)⁻¹ = b⁻¹ * a⁻¹ := by
  have h : (b⁻¹ * a⁻¹) * (a*b) = e := by
    calc (b⁻¹ * a⁻¹) * (a*b)
        = ((b⁻¹ * a⁻¹) * a) * b := by rw [← MyGroup.mul_assoc]
      _ = (b⁻¹ * (a⁻¹ * a)) * b := by rw [← MyGroup.mul_assoc]
      _ = (b⁻¹ * e) * b := by rw [MyGroup.mul_left_inv]
      _ = b⁻¹ * b := by rw [MyGroup.mul_one]
      _ = e := by rw [MyGroup.mul_left_inv]
  exact (left_inv_unique (a*b) (b⁻¹ * a⁻¹) h).symm

theorem MyGroup.cancellation_left (a b c : G) : a * b = a * c → b = c := by
  intro h
  calc b = e * b           := by rw [MyGroup.one_mul]
       _ = (a⁻¹ * a) * b   := by rw [MyGroup.mul_left_inv]
       _ = a⁻¹ * (a * b)   := by rw [MyGroup.mul_assoc]
       _ = a⁻¹ * (a * c)   := by rw [h]
       _ = (a⁻¹ * a) * c   := by rw [MyGroup.mul_assoc]
       _ = e * c           := by rw [MyGroup.mul_left_inv]
       _ = c               := by rw [MyGroup.one_mul]

--------------------------------------------
-- Subgroups
--------------------------------------------
structure MySubgroup (G : Type) [MyGroup G] where
  carrier : Set G
  mul_mem : ∀ {a b}, a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  one_mem : e ∈ carrier
  inv_mem : ∀ {a}, a ∈ carrier → a⁻¹ ∈ carrier

instance : Membership G (MySubgroup G) where
  mem (H : MySubgroup G) (x : G)  := x ∈ H.carrier

example (H : MySubgroup G) (x y : G) (hx : x ∈ H) (hy : y ∈ H) :
  x * y ∈ H := by
  apply H.mul_mem hx hy


-- Example: ℝ* is a group, and ℚ* is a subgroup of ℝ*
def R_Star : Type := { x : ℝ // x ≠ 0 }

-- an element in R* looks like ⟨x ∈ ℝ, a proof of x ≠ 0⟩
-- proof of R* is a group:
noncomputable instance : MyGroup R_Star where
  mul a b := ⟨a.val * b.val, mul_ne_zero a.property b.property⟩
  one := ⟨1, one_ne_zero⟩
  inv a := ⟨a.val⁻¹, inv_ne_zero a.property⟩
  mul_assoc a b c := Subtype.ext (mul_assoc a.val b.val c.val)
  one_mul a       := Subtype.ext (one_mul a.val)
  mul_one a       := Subtype.ext (mul_one a.val)
  mul_left_inv a  := by
    apply Subtype.ext
    exact inv_mul_cancel₀ a.property
  mul_right_inv a := by
    apply Subtype.ext
    exact mul_inv_cancel₀ a.property
--exercise: show that R* is an AbelianGroup

def rational_reals : Set R_Star :=
  { x | ∃ q : ℚ, q ≠ 0 ∧ x.val = (q : ℝ) }

def Q_Star_subgroup : MySubgroup R_Star where
  carrier := rational_reals
  one_mem := by
    dsimp [rational_reals]
    use 1
    constructor
    · exact one_ne_zero
    · norm_cast
  mul_mem := by
    intro a b ha hb
    dsimp [rational_reals, MyGroup.mul]
    rcases ha with ⟨qa, hqa_ne, hqa_val⟩
    rcases hb with ⟨qb, hqb_ne, hqb_val⟩
    use qa * qb
    constructor
    · exact mul_ne_zero hqa_ne hqb_ne
    · rw [hqa_val, hqb_val]
      norm_cast
  inv_mem := by
    intro a ha
    dsimp [rational_reals, MyGroup.inv]
    rcases ha with ⟨q, hq_ne, hq_val⟩
    use q⁻¹
    constructor
    · exact inv_ne_zero hq_ne
    · rw [hq_val]
      norm_cast

-- If G and H are groups, G × H is a group.
instance {G H : Type} [MyGroup G] [MyGroup H] : MyGroup (G × H) where
  mul a b := (a.1 * b.1, a.2 * b.2)
  one := (e, e)
  inv a := (a.1⁻¹, a.2⁻¹)
  mul_assoc := by
    intros a b c
    ext
    · apply MyGroup.mul_assoc
    · apply MyGroup.mul_assoc
  one_mul := by
    intros
    ext <;>
    apply MyGroup.one_mul
  mul_one := by
    intros
    ext <;>
    apply MyGroup.mul_one
  mul_left_inv := by
    intros
    ext <;>
    apply MyGroup.mul_left_inv
  mul_right_inv := by
    intros
    ext <;>
    apply MyGroup.mul_right_inv
