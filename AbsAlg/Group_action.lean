import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Coset.Card

noncomputable section

/-
Definition of a group action of a group G on a set X.
-/
structure MyGroupAction (G : Type*) (X : Type*) [Group G] where
  act : G → X → X
  one_act : ∀ x : X, act 1 x = x
  mul_act : ∀ (g h : G) (x : X), act (g * h) x = act g (act h x)

def orbit {G X : Type*} [Group G] (A : MyGroupAction G X) (x : X) : Set X :=
  { y | ∃ g : G, A.act g x = y }

def stabilizer {G X : Type*} [Group G] (A : MyGroupAction G X) (x : X) : Subgroup G where
  carrier := { g | A.act g x = x }
  one_mem' := A.one_act x
  mul_mem' := by
    intro a b ha hb
    dsimp -- Exposes the goal as: A.act (a * b) x = x
    rw [A.mul_act] -- A.act a (A.act b x) = x
    rw [hb]        -- A.act a x = x
    rw [ha]        -- x = x
  inv_mem' := by
    intro g hg
    dsimp
    calc A.act g⁻¹ x
      _ = A.act g⁻¹ (A.act g x) := by rw [hg] -- Replace x with (act g x)
      _ = A.act (g⁻¹ * g) x     := by rw [← A.mul_act] -- Collapse the action
      _ = A.act 1 x             := by rw [inv_mul_cancel]
      _ = x                     := by rw [A.one_act]

#check fun {G : Type*} [Group G] (H : Subgroup G) => G ⧸ H


def orbit_map {G X : Type*} [Group G] (A : MyGroupAction G X) (x : X) :
    G ⧸ stabilizer A x → orbit A x :=
  Quotient.lift (fun g => ⟨A.act g x, ⟨g, rfl⟩⟩) (by
    intro a b hab
    simp only [Subtype.mk.injEq]
    -- 1. Convert the relation a ≈ b into an equality of quotient classes: ⟦a⟧ = ⟦b⟧
    -- This works regardless of how ≈ is internally represented.
    let q_eq : QuotientGroup.mk a = QuotientGroup.mk b := Quotient.sound hab
    -- 2. Use the standard group theory lemma to convert ⟦a⟧ = ⟦b⟧ into a⁻¹ * b ∈ Stabilizer
    rw [QuotientGroup.eq] at q_eq
    -- 3. Now q_eq is exactly: a⁻¹ * b ∈ stabilizer A x
    -- This means acting by (a⁻¹ * b) fixes x.
    have h_stab : A.act (a⁻¹ * b) x = x := q_eq
    -- 4. Finish the calculation
    calc A.act a x
      _ = A.act a (A.act (a⁻¹ * b) x) := by rw [h_stab]
      _ = A.act (a * (a⁻¹ * b)) x     := by rw [← A.mul_act]
      _ = A.act b x                   := by simp
  )

theorem orbit_stabilizer_theorem {G X : Type*} [Group G] (A : MyGroupAction G X) (x : X) :
  Function.Bijective (orbit_map A x) := by
  constructor
  · intro qa qb h_eq
    revert qa qb
    intro qa qb
    refine Quotient.inductionOn₂ qa qb ?_
    intro a b h_eq
    -- Now we are working with standard group elements a and b
    simp only [orbit_map, Quotient.lift_mk, Subtype.ext_iff] at h_eq
    -- Goal: Prove ⟦a⟧ = ⟦b⟧, which is equivalent to a⁻¹ * b ∈ Stabilizer
    apply QuotientGroup.eq.mpr
    -- Definition of Stabilizer: act (a⁻¹ * b) x = x
    change A.act (a⁻¹ * b) x = x
    calc A.act (a⁻¹ * b) x
      _ = A.act a⁻¹ (A.act b x) := by rw [A.mul_act]
      _ = A.act a⁻¹ (A.act a x) := by rw [h_eq]
      _ = A.act (a⁻¹ * a) x     := by rw [← A.mul_act]
      _ = A.act 1 x             := by rw [inv_mul_cancel]
      _ = x                     := by rw [A.one_act]
  · intro ⟨y, hy⟩
    obtain ⟨g, rfl⟩ := hy
    use ⟦g⟧
    rfl

def fixed_points {G X : Type*} [Group G] (A : MyGroupAction G X) (g : G) : Set X :=
  { x | A.act g x = x }

def orbits {G X : Type*} [Group G] (A : MyGroupAction G X) : Set (Set X) :=
  { o | ∃ x, o = orbit A x }


open BigOperators
open Classical

-- Summing 1/|Orbit(x)| counts the number of orbits.
-- Intuition: If an orbit has 5 elements, we sum 1/5 five times, getting 1.
lemma sum_inv_orbit_eq_orbits {G X : Type*} [Group G] [Fintype X] (A : MyGroupAction G X) :
    ∑ x : X, (1 : ℚ) / Fintype.card (orbit A x) = Fintype.card (orbits A) := by
  have h_orbit_sum : ∑ x : X, (1 / (Fintype.card (orbit A x) : ℚ))
                  = ∑ o ∈ Finset.image (fun x : X => orbit A x) Finset.univ, (1 : ℚ) := by
    rw [ Finset.sum_image' ];
    intro x hx
    have h_card : Fintype.card (orbit A x) =
                  Finset.card (Finset.filter (fun y => orbit A y = orbit A x) Finset.univ) := by
      rw [ Fintype.card_of_subtype ];
      intro y
      simp only [orbit, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor;
      · intro h;
        exact h.subset ⟨ 1, by simp [ A.one_act ] ⟩;
      · rintro ⟨ g, rfl ⟩;
        ext y;
        constructor <;> rintro ⟨ h, rfl ⟩;
        · exact ⟨ h * g, by rw [ A.mul_act ] ⟩;
        · exact ⟨ h * g⁻¹, by simp [ ← A.mul_act ] ⟩;
    rw [ Finset.sum_congr rfl fun y hy => by
        rw [ show orbit A y = orbit A x from Finset.mem_filter.mp hy |>.2 ] ]
    aesop
  convert h_orbit_sum using 1
  simp only [Fintype.card_ofFinset, Finset.sum_const, nsmul_eq_mul, mul_one, orbits,
    Set.coe_setOf] at *
  rw [ Fintype.card_of_subtype ]
  aesop

variable {G X : Type*} [Group G] [Fintype G] [Fintype X] (A : MyGroupAction G X)

lemma card_orbit_mul_card_stabilizer (x : X) :
    Fintype.card (orbit A x) * Fintype.card (stabilizer A x) = Fintype.card G := by
  have h_orbit_eq_quotient :
      Fintype.card (orbit A x) = Fintype.card (G ⧸ stabilizer A x) :=
    Fintype.card_congr (Equiv.ofBijective _ (orbit_stabilizer_theorem A x)).symm
  have h_lagrange :
      Fintype.card G = Fintype.card (G ⧸ stabilizer A x) * Fintype.card (stabilizer A x) := by
    have h:= Subgroup.card_eq_card_quotient_mul_card_subgroup (stabilizer A x)
    simp only [Nat.card_eq_fintype_card] at h
    exact h
  rw [h_orbit_eq_quotient]
  linarith

/-
Burnside's Lemma: The number of orbits times the size of the group
is equal to the sum of the number of fixed points for each group element.
-/
theorem burnside_lemma :
    (Fintype.card (orbits A) : ℚ) * Fintype.card G = ∑ g : G, Fintype.card (fixed_points A g) := by
  have h_burnside : (Fintype.card (orbits A) : ℚ)
            = (∑ g : G, (Fintype.card (fixed_points A g)) : ℚ) / (Fintype.card G : ℚ) := by
    -- By interchanging the order of summation, we can rewrite
    -- the sum as $\sum_{x \in X} | \text{Stab}(x) |$.
    have h_interchange : (∑ g : G, Fintype.card (fixed_points A g) : ℚ)
                        = (∑ x : X, Fintype.card (stabilizer A x) : ℚ) := by
      simp only [fixed_points, Fintype.card_subtype];
      simp only [Finset.card_filter, stabilizer];
      exact mod_cast Finset.sum_comm;
    -- By the orbit-stabilizer theorem, we know that
    -- $| \text{Stab}(x) | = \frac{| G |}{| \text{Orb}(x) |}$.
    have h_orbit_stabilizer : ∀ x : X, Fintype.card (stabilizer A x)
                          = (Fintype.card G : ℚ) / (Fintype.card (orbit A x) : ℚ) := by
      intro x
      have h_orbit_stabilizer : Fintype.card (stabilizer A x) * Fintype.card (orbit A x)
                                = Fintype.card G := by
        rw [ mul_comm, card_orbit_mul_card_stabilizer ];
      -- Since the orbit of x is non-empty, we can divide
      -- both sides of the equation by the cardinality of the orbit.
      have h_nonzero : Fintype.card (orbit A x) ≠ 0 := by
        simp only [Fintype.card_ofFinset, ne_eq, Finset.card_eq_zero,
          Finset.filter_eq_empty_iff, Finset.mem_univ, forall_const, not_forall,
          Decidable.not_not] at *
        exact ⟨ _, ⟨ 1, rfl ⟩ ⟩
      exact eq_div_of_mul_eq ( Nat.cast_ne_zero.mpr h_nonzero ) ( mod_cast h_orbit_stabilizer );
    have h := sum_inv_orbit_eq_orbits A
    simp_all [ div_eq_mul_inv, mul_comm, Finset.mul_sum _ _ _ ]
  rw [ h_burnside, div_mul_cancel₀ _ ( Nat.cast_ne_zero.mpr Fintype.card_ne_zero ) ]
  norm_cast
