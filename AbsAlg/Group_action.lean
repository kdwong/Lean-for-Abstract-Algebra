import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import Mathlib.Data.Fintype.Card

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
  one_mem' := by
    exact A.one_act x
  mul_mem' := by
    intro a b ha hb
    have h1 : A.act (a * b) x = A.act a (A.act b x) := by
      exact A.mul_act a b x;
    grind
  inv_mem' := by
    intro g hg
    calc A.act g⁻¹ x
      = A.act g⁻¹ (A.act g x) := by rw [hg]
    _ = A.act (g⁻¹ * g) x := by rw [← A.mul_act]
    _ = A.act 1 x := by rw [inv_mul_cancel]
    _ = x := by rw [A.one_act]

#check fun {G : Type*} [Group G] (H : Subgroup G) => G ⧸ H


def orbit_map {G X : Type*} [Group G] (A : MyGroupAction G X) (x : X) :
    G ⧸ stabilizer A x → orbit A x :=
  Quotient.lift (fun g => ⟨A.act g x, ⟨g, rfl⟩⟩) (by
    intro a b hab
    rcases hab with ⟨g, hg⟩
    obtain ⟨g, g_stab⟩ := g
    simp only [← hg, Subgroup.mk_smul, MulOpposite.smul_eq_mul_unop, Subtype.mk.injEq]
    rw [A.mul_act]
    have : A.act (MulOpposite.unop g) x = x := g_stab
    rw [this])



theorem orbit_stabilizer_theorem {G X : Type*} [Group G] (A : MyGroupAction G X) (x : X) :
  Function.Bijective (orbit_map A x) := by
    unfold orbit_map;
    constructor;
    · intro a b hop;
      obtain ⟨ g, rfl ⟩ := Quotient.exists_rep a
      obtain ⟨ h, rfl ⟩ := Quotient.exists_rep b
      simp_all +decide only [Quotient.lift_mk,Subtype.ext_iff]
      have h_inv_g_in_stab : h⁻¹ * g ∈ stabilizer A x := by
        have h_inv_g_in_stab : A.act (h⁻¹ * g) x = x := by
          have h_inv_g_in_stab : A.act (h⁻¹ * g) x = A.act h⁻¹ (A.act g x) := by
            exact A.mul_act _ _ _;
          have h_inv_g_in_stab : A.act h⁻¹ (A.act h x) = x := by
            rw [ ← A.mul_act, inv_mul_cancel, A.one_act ]
          grind
        exact h_inv_g_in_stab
      rw [ QuotientGroup.eq ]
      convert Subgroup.inv_mem _ h_inv_g_in_stab using 1
      group
    · intro ⟨ y, hy ⟩;
      rcases hy with ⟨ g, rfl ⟩ ; exact ⟨ ⟦g⟧, rfl ⟩

def fixed_points {G X : Type*} [Group G] (A : MyGroupAction G X) (g : G) : Set X :=
  { x | A.act g x = x }

def orbits {G X : Type*} [Group G] (A : MyGroupAction G X) : Set (Set X) :=
  { o | ∃ x, o = orbit A x }


/-
Burnside's Lemma: The number of orbits times the size of the group
is equal to the sum of the number of fixed points for each group element.
-/
open Classical in
theorem burnside_lemma {G X : Type*} [Group G] [Fintype G] [Fintype X] (A : MyGroupAction G X) :
  Fintype.card (orbits A) * Fintype.card G = ∑ g : G, Fintype.card (fixed_points A g) := by
    set S : Set (G × X) := {p | A.act p.1 p.2 = p.2} with hS_def
    -- We count the size of $S$ in two ways.
    -- First, summing over $g \in G$, for a fixed $g$.
    have hS_card : Fintype.card S = ∑ g : G, Fintype.card (fixed_points A g) := by
      simp only [hS_def, Fintype.card_ofFinset, fixed_points]
      simp only [Finset.card_filter]
      exact Fintype.sum_prod_type fun x ↦ if x ∈ {p | A.act p.1 p.2 = p.2} then 1 else 0;
    -- Now, summing over $x \in X$, for a fixed $x$.
    have hS_card' : Fintype.card S = ∑ x : X, Fintype.card (stabilizer A x) := by
      simp only [Fintype.card_subtype, Finset.card_filter]
      exact Fintype.sum_prod_type_right fun x ↦ if x ∈ S then 1 else 0;
    -- Applu Orbit-Stabilizer Theorem.
    have h_orbit_stabilizer : ∀ x : X, Fintype.card G =
                                    Fintype.card (orbit A x) * Fintype.card (stabilizer A x) := by
      intro x
      have h_orbit_stabilizer : Fintype.card (orbit A x) = Fintype.card (G ⧸ stabilizer A x) := by
        convert Fintype.card_congr ( Equiv.ofBijective ( orbit_map A x )
                                        ( orbit_stabilizer_theorem A x ) ) |> Eq.symm using 1
      have h_card_G : Fintype.card G =
                      Fintype.card (G ⧸ stabilizer A x) * Fintype.card (stabilizer A x) := by
        have := Subgroup.card_eq_card_quotient_mul_card_subgroup ( stabilizer A x ) ; aesop;
      rw [h_orbit_stabilizer] at *; exact h_card_G;
    -- Let $\mathcal{O}$ be the set of orbits.
    set O := orbits A with hO_def
    -- Then, $∑_{x \in X} 1/|orbit(x)| = \sum_{o \in O} \sum_{x \in O} \frac{1}{|O|}$.
    have h_sum_orbits : ∑ x : X, (1 / Fintype.card (orbit A x) : ℚ) =
                            ∑ O ∈ Finset.image (fun x => orbit A x) Finset.univ, (1 : ℚ) := by
      rw [ Finset.sum_image' ];
      intro x _
      rw [ Finset.sum_congr rfl fun y hy =>
            by rw [ show orbit A y = orbit A x from Finset.mem_filter.mp hy |>.2 ] ]
      simp only [Fintype.card_ofFinset, one_div, Finset.sum_const, nsmul_eq_mul]
      rw [ ← div_eq_mul_inv, eq_div_iff ] <;>
      norm_cast <;>
      simp? [Finset.card_univ]
      · congr 1 with y
        simp only [orbit, Finset.mem_filter, Finset.mem_univ, Set.mem_setOf_eq, true_and]
        constructor <;> intro h
        · ext z
          obtain ⟨ g, rfl ⟩ := h
          simp only [← A.mul_act, Set.mem_setOf_eq]
          exact ⟨ fun ⟨ h, hh ⟩ => ⟨ h * g, hh ⟩,
                fun ⟨ h, hh ⟩ => ⟨ h * g⁻¹, by simpa [ ← A.mul_act ] using hh ⟩ ⟩
        · exact h.subset ⟨ 1, by simp +decide [ A.one_act ] ⟩
      · exact ⟨ _, ⟨ 1, A.one_act x ⟩ ⟩

    have h_sum_rewrite : ∑ x : X, Fintype.card (stabilizer A x) =
                              Fintype.card G * ∑ x : X, (1 / Fintype.card (orbit A x) : ℚ) := by
      push_cast [ Finset.mul_sum _ _ _ ]
      exact Finset.sum_congr rfl fun x _ => by rw [ mul_one_div, eq_div_iff ] <;>
      norm_cast <;> nlinarith [ h_orbit_stabilizer x, show 0 < Fintype.card ( orbit A x ) from Fintype.card_pos_iff.mpr ⟨ _, ⟨ 1, rfl ⟩ ⟩ ] ;
    rw [ ← @Nat.cast_inj ℚ ] at *
    simp_all only [Set.coe_setOf, Fintype.card_ofFinset, Nat.cast_sum, one_div, mul_comm,
      Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_mul]
    rw [ mul_comm ]
    congr
    ext
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    exact ⟨ fun ⟨ x, hx ⟩ => ⟨ x, hx.symm ⟩, fun ⟨ x, hx ⟩ => ⟨ x, hx.symm ⟩ ⟩
