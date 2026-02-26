import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import Mathlib.Data.Fintype.Card


/-
Definition of a subgroup and a normal subgroup for a subset H of a group G.
-/
def IsSubgroup {G : Type*} [Group G] (H : Set G) : Prop :=
  H 1 ∧ (∀ x y, H x → H y → H (x * y)) ∧ (∀ x, H x → H x⁻¹)

def IsNormal {G : Type*} [Group G] (H : Set G) : Prop :=
  IsSubgroup H ∧ ∀ g h, H h → H (g * h * g⁻¹)

/-
We use equivalence relation to define left coset. The def below doesn't require H ≤ G yet.
-/
def LeftCosetRel {G : Type*} [Group G] (H : Set G) (x y : G) : Prop :=
  H (x⁻¹ * y)

/-
Now we need H ≤ G to see this is an equivalence relation.
-/
theorem LeftCosetRel_equiv {G : Type*} [Group G]
    (H : Set G) (hH : IsSubgroup H) : Equivalence (LeftCosetRel H) := by
  constructor
  · simp_all only [LeftCosetRel, inv_mul_cancel]
    intro x
    exact hH.1
  · intro x
    exact fun { y } hy => by simpa [ mul_assoc ] using hH.2.2 ( x⁻¹ * y ) hy
  · intros x y z hy hz
    have h_prod : H ((x⁻¹ * y) * (y⁻¹ * z)) := by
      exact hH.2.1 _ _ hy hz
    simpa [ mul_assoc ] using h_prod

/-
Definition of the Setoid ("equivalence class") structure on G by left cosets of H.
-/
def LeftCosetSetoid {G : Type*} [Group G] (H : Set G) (hH : IsSubgroup H) : Setoid G :=
  { r := LeftCosetRel H, iseqv := LeftCosetRel_equiv H hH }

/-
Theorem stating that multiplication is well-defined on the quotient by a normal subgroup.
That is, if aH = a'H and bH = b'H, then abH = a'b'H.
-/
theorem mul_well_defined {G : Type*} [Group G] (H : Set G) (hH : IsSubgroup H) (hN : IsNormal H)
    (a b a' b' : G) (ha : LeftCosetRel H a a') (hb : LeftCosetRel H b b') :
    LeftCosetRel H (a * b) (a' * b') := by
      have h_normal : ∀ g h, H h → H (g * h * g⁻¹) := by
        exact hN.2
      obtain ⟨h_a, ha_eq⟩ : ∃ h_a, a' = a * h_a ∧ H h_a := by
        exact ⟨ a⁻¹ * a', by group, ha ⟩
      obtain ⟨h_b, hb_eq⟩ : ∃ h_b, b' = b * h_b ∧ H h_b := by
        exact ⟨ b⁻¹ * b', by group, by simpa using hb ⟩
      simp_all only [LeftCosetRel, inv_mul_cancel_left, mul_assoc, mul_inv_rev]
      convert hH.2.1 _ _ ( h_normal b⁻¹ h_a ha_eq.2 ) ( hb_eq.2 ) using 1
      group

/-
Definition of the quotient group type and its multiplication operation,
using a local instance for the setoid.
-/
def MyQuotientGroup {G : Type*} [Group G] (H : Set G) (hH : IsSubgroup H) :=
    Quotient (LeftCosetSetoid H hH)

def MyQuotientGroup.mk {G : Type*} [Group G] (H : Set G) (hH : IsSubgroup H) (x : G) :
    MyQuotientGroup H hH :=  Quotient.mk (LeftCosetSetoid H hH) x

def MyQuotientGroup.mul {G : Type*} [Group G] (H : Set G) (hH : IsSubgroup H) (hN : IsNormal H) :
    MyQuotientGroup H hH → MyQuotientGroup H hH → MyQuotientGroup H hH :=
  letI : Setoid G := LeftCosetSetoid H hH
  Quotient.lift₂ (fun x y => MyQuotientGroup.mk H hH (x * y))
    (fun a b a' b' ha hb => Quotient.sound (mul_well_defined H hH hN a b a' b' ha hb))

def MyQuotientGroup.one {G : Type*} [Group G] (H : Set G) (hH : IsSubgroup H) :
  MyQuotientGroup H hH :=  MyQuotientGroup.mk H hH 1

def MyQuotientGroup.inv {G : Type*} [Group G] (H : Set G) (hH : IsSubgroup H) (hN : IsNormal H) :
    MyQuotientGroup H hH → MyQuotientGroup H hH :=
  letI : Setoid G := LeftCosetSetoid H hH
  Quotient.lift (fun x => MyQuotientGroup.mk H hH x⁻¹)
  (fun a b hab => Quotient.sound (by
  obtain ⟨h, hh⟩ : ∃ h ∈ H, a⁻¹ * b = h := by
    exact ⟨ _, hab, rfl ⟩
  have h_inv : h⁻¹ ∈ H := by
    exact hH.2.2 _ hh.1;
  have hb_inv : b⁻¹ = h⁻¹ * a⁻¹ := by
    simp [ ← hh.2, mul_assoc ]
  have h_mul : (a⁻¹)⁻¹ * b⁻¹ ∈ H := by
    have := hN.2 a ( h⁻¹ ) h_inv
    simp_all only [mul_assoc, inv_inv]
    exact this
  exact h_mul))

/-
Left identity property for the quotient group multiplication.
-/
theorem MyQuotientGroup.one_mul {G : Type*} [Group G] (H : Set G)
      (hH : IsSubgroup H) (hN : IsNormal H) : ∀ x : MyQuotientGroup H hH,
    MyQuotientGroup.mul H hH hN (MyQuotientGroup.one H hH) x = x := by
      unfold MyQuotientGroup.mul MyQuotientGroup.one
      generalize_proofs at *;
      intro x
      refine Quotient.inductionOn x (fun x => ?_)
      simp [MyQuotientGroup.mk]

/-
Right identity property for the quotient group multiplication.
-/
theorem MyQuotientGroup.mul_one {G : Type*} [Group G] (H : Set G)
    (hH : IsSubgroup H) (hN : IsNormal H) : ∀ x : MyQuotientGroup H hH,
    MyQuotientGroup.mul H hH hN x (MyQuotientGroup.one H hH) = x := by
      intro x
      refine Quotient.inductionOn x (fun x => ?_)
      erw [ Quotient.eq'' ];
      have h_coset : x⁻¹ * (x * 1) ∈ H := by
        simpa using hH.1;
      exact Setoid.symm' (LeftCosetSetoid H hH) h_coset

/-
Left inverse property for the quotient group multiplication.
-/
theorem MyQuotientGroup.inv_mul_cancel {G : Type*} [Group G] (H : Set G)
    (hH : IsSubgroup H) (hN : IsNormal H) : ∀ x : MyQuotientGroup H hH,
    MyQuotientGroup.mul H hH hN (MyQuotientGroup.inv H hH hN x) x = MyQuotientGroup.one H hH := by
      intro x
      refine Quotient.inductionOn x (fun x => ?_)
      exact Quotient.sound ( by simp )

/-
Helper lemma stating that multiplication of representatives corresponds
to multiplication in the group.
-/
theorem MyQuotientGroup.mk_mul {G : Type*} [Group G] (H : Set G)
(hH : IsSubgroup H) (hN : IsNormal H) (a b : G) : MyQuotientGroup.mul H hH hN
(MyQuotientGroup.mk H hH a) (MyQuotientGroup.mk H hH b) = MyQuotientGroup.mk H hH (a * b) := by
      convert Quotient.map₂_mk ( fun x y => x * y ) _ _ _;
      exact fun a b hab c d hcd => mul_well_defined H hH hN a c b d hab hcd

/-
Test theorem to verify Quotient.inductionOn functionality.
-/
theorem test_induction {G : Type*} [Group G] (H : Set G)
(hH : IsSubgroup H) (x : MyQuotientGroup H hH) : x = x := by
  rfl

/-
Induction principle for the quotient group.
-/
theorem MyQuotientGroup.inductionOn {G : Type*} [Group G] (H : Set G) (hH : IsSubgroup H)
    {p : MyQuotientGroup H hH → Prop} (x : MyQuotientGroup H hH)
    (h : ∀ a : G, p (MyQuotientGroup.mk H hH a)) : p x := by
  letI : Setoid G := LeftCosetSetoid H hH
  exact Quotient.inductionOn x h

/-
Associativity of multiplication in the quotient group.
-/
theorem MyQuotientGroup.mul_assoc {G : Type*} [Group G] (H : Set G)
  (hH : IsSubgroup H) (hN : IsNormal H) : ∀ x y z : MyQuotientGroup H hH,
    MyQuotientGroup.mul H hH hN (MyQuotientGroup.mul H hH hN x y) z =
    MyQuotientGroup.mul H hH hN x (MyQuotientGroup.mul H hH hN y z) := by
  intro x y z
  apply MyQuotientGroup.inductionOn H hH x
  intro a
  apply MyQuotientGroup.inductionOn H hH y
  intro b
  apply MyQuotientGroup.inductionOn H hH z
  intro c
  repeat rw [MyQuotientGroup.mk_mul]
  rw [_root_.mul_assoc]

/-
Instance of the Group typeclass for the quotient group.
-/
instance {G : Type*} [Group G] (H : Set G) (hH : IsSubgroup H)
  (hN : IsNormal H) : Group (MyQuotientGroup H hH) :=
  { mul := MyQuotientGroup.mul H hH hN
    one := MyQuotientGroup.one H hH
    inv := MyQuotientGroup.inv H hH hN
    mul_assoc := MyQuotientGroup.mul_assoc H hH hN
    one_mul := MyQuotientGroup.one_mul H hH hN
    mul_one := MyQuotientGroup.mul_one H hH hN
    inv_mul_cancel := MyQuotientGroup.inv_mul_cancel H hH hN }
