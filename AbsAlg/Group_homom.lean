import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import Mathlib.Data.Fintype.Card


/-
In Lean, group homomorphism is denoted as f: G →* H
-/
def kernel_set {G H : Type*} [Group G] [Group H] (f : G →* H) : Set G := {x | f x = 1}

def image_set {G H : Type*} [Group G] [Group H] (f : G →* H) : Set H := {y | ∃ x, f x = y}


theorem kernel_is_subgroup {G H : Type*} [Group G] [Group H] (f : G →* H) :
  let K := kernel_set f
  (1 : G) ∈ K ∧ (∀ x y, x ∈ K → y ∈ K → x * y ∈ K) ∧ (∀ x, x ∈ K → x⁻¹ ∈ K) := by
    have h1 : 1 ∈ kernel_set f := by
      exact f.map_one;
    exact ⟨ h1, fun x y hx hy => by
    simp_all [ kernel_set ], fun x hx => by simp_all [ kernel_set ] ⟩

theorem kernel_is_normal {G H : Type*} [Group G] [Group H] (f : G →* H) :
  let K := kernel_set f
  ∀ g : G, ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    simp_all [ mul_assoc, kernel_set ]

/-
The image of a group homomorphism forms a subgroup.
-/
theorem image_is_subgroup {G H : Type*} [Group G] [Group H] (f : G →* H) :
  let I := image_set f
  (1 : H) ∈ I ∧ (∀ x y, x ∈ I → y ∈ I → x * y ∈ I) ∧ (∀ x, x ∈ I → x⁻¹ ∈ I) := by
    exact ⟨ ⟨ 1, by simp +decide ⟩, fun x y hx hy => by
    rcases hx with ⟨ x, rfl ⟩
    rcases hy with ⟨ y, rfl ⟩
    exact ⟨ x * y, by simp +decide ⟩, fun x hx => by
    rcases hx with ⟨ x, rfl ⟩ ; exact ⟨ x⁻¹, by simp +decide ⟩ ⟩


/-
Now we prove first isomorphism theorem. Begin by defining the map from G/ker(f) to im(f).
-/
noncomputable def firstIsoMap {G H : Type*} [Group G] [Group H] (f : G →* H) :
  G ⧸ f.ker →* f.range := QuotientGroup.lift f.ker f.rangeRestrict (by intro g hg; aesop)

/-
The induced map is bijective.
-/
theorem firstIsoMap_bijective {G H : Type*} [Group G] [Group H] (f : G →* H) :
  Function.Bijective (firstIsoMap f) := by
  constructor
  · intro x y
    refine QuotientGroup.induction_on x (fun x' => ?_)
    refine QuotientGroup.induction_on y (fun y' => ?_)
    simp [firstIsoMap, Subtype.ext_iff, QuotientGroup.eq]
    aesop
  · intro x;
    rcases x with ⟨ x, ⟨ g, rfl ⟩ ⟩
    use QuotientGroup.mk g
    aesop

/-
The first isomorphism theorem: G/ker(f) is isomorphic to im(f).
-/
noncomputable def firstIso {G H : Type*} [Group G] [Group H] (f : G →* H) :
    G ⧸ f.ker ≃* f.range :=
  MulEquiv.ofBijective (firstIsoMap f) (firstIsoMap_bijective f)
