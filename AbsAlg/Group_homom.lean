import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic


/-
In Lean, group homomorphism is denoted as f: G →* H
-/
def kernel_set {G H : Type*} [Group G] [Group H] (f : G →* H) : Set G := {x | f x = 1}

def image_set {G H : Type*} [Group G] [Group H] (f : G →* H) : Set H := {y | ∃ x, f x = y}

def kernel_subgroup {G H : Type*} [Group G] [Group H] (f : G →* H) : Subgroup G :=
{
  carrier := kernel_set f,
  one_mem' := by
    simp [kernel_set],
  mul_mem' := by
    intro k1 k2 hk1 hk2
    simp_all [kernel_set, Set.mem_setOf_eq, map_mul, mul_one]
  inv_mem' := by
    intro k hk
    -- hk : f k = 1
    simp_all [kernel_set, map_inv]
}

instance kernel_subgroup_normal {G H : Type*} [Group G] [Group H] (f : G →* H) :
  (kernel_subgroup f).Normal := by
  classical
  refine ⟨?_⟩
  intro x hx g
  simp [kernel_subgroup, kernel_set] at *
  simp [hx]

/-
The image of a group homomorphism forms a subgroup.
-/
def image_subgroup {G H : Type*} [Group G] [Group H]
  (f : G →* H) : Subgroup H :=
{
  carrier := image_set f,
  one_mem' := by
    simp only [image_set, Set.mem_setOf_eq]
    exact ⟨1, by simp⟩
  mul_mem' := by
    intro y₁ y₂ hy₁ hy₂
    rcases hy₁ with ⟨x₁, rfl⟩
    rcases hy₂ with ⟨x₂, rfl⟩
    simp only [image_set, Set.mem_setOf_eq]
    exact ⟨x₁ * x₂, by simp [map_mul]⟩
  inv_mem' := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    simp only [image_set, Set.mem_setOf_eq]
    exact ⟨x⁻¹, by simp [map_inv]⟩
}

/-
Now we prove first isomorphism theorem. Begin by defining the map from G/ker(f) to im(f).
-/
def firstIsoMap {G H : Type*} [Group G] [Group H] (f : G →* H) :
  G ⧸ kernel_subgroup f →* image_subgroup f := by
  classical
  -- Step 1: define map into image
  let φ : G →* image_subgroup f :=
  { toFun := fun g => ⟨f g, ⟨g, rfl⟩⟩,
    map_one' := by
      ext
      simp,
    map_mul' := by
      intro a b
      ext
      simp [map_mul],
  }
  -- Step 2: prove kernel condition
  have hker :
    ∀ x ∈ kernel_subgroup f, φ x = 1 := by
    intro x hx
    ext
    simp [φ, kernel_subgroup, kernel_set] at *
    simp [hx]
  -- Step 3: lift to quotient
  exact QuotientGroup.lift (kernel_subgroup f) φ hker

/-
The induced map is bijective.
-/
theorem firstIsoMap_bijective {G H : Type*} [Group G] [Group H] (f : G →* H) :
  Function.Bijective (firstIsoMap f) := by
  constructor
  · unfold Function.Injective
    intro x y
    refine QuotientGroup.induction_on x (fun x' => ?_)
    refine QuotientGroup.induction_on y (fun y' => ?_)
    simp only [firstIsoMap, QuotientGroup.lift_mk, MonoidHom.coe_mk, OneHom.coe_mk, Subtype.ext_iff,
      QuotientGroup.eq]
    intro h
    simp only [kernel_subgroup, kernel_set, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
      Set.mem_setOf_eq, map_mul, map_inv]
    have h' : (f x')⁻¹ * (f y') = 1 := by
      simp only [h]
      aesop
    exact h'
  · intro x
    rcases x with ⟨ x, ⟨ g, rfl ⟩ ⟩
    use QuotientGroup.mk g
    aesop

/-
The first isomorphism theorem: G/ker(f) is isomorphic to im(f).
-/
noncomputable def firstIso {G H : Type*} [Group G] [Group H] (f : G →* H) :
    G ⧸ f.ker ≃* f.range :=
  MulEquiv.ofBijective (firstIsoMap f) (firstIsoMap_bijective f)
