import Mathlib.Tactic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Data.List.Induction
import Mathlib.Algebra.Ring.Parity

open Equiv Perm

-- Here the permutation group is defined as (Perm α), where α can be any set
-- If we take α = Fin n, we will get Sₙ

variable {α : Type*} [DecidableEq α]

lemma swap_mul_swap_comm_of_disjoint {a b c d : α}
    (h : Disjoint ({a, b} : Set α) {c, d}) :
    swap a b * swap c d = swap c d * swap a b := by
      ext x
      simp [ Equiv.swap_apply_def ]
      aesop

lemma swap_mul_swap_share_left {a b c : α} (hcb : c ≠ b) (hca : c ≠ a) :
    swap a c * swap a b = swap a b * swap b c := by
      ext x
      by_cases h : x = a <;>
      by_cases h' : x = b <;>
      by_cases h'' : x = c <;>
      simp [ *, Equiv.swap_apply_def ]
      · grind
      · grind
      · grind
      · grind

lemma swap_mul_swap_share_right {a b d : α} (hda : d ≠ a) (hdb : d ≠ b) (hab : a ≠ b) :
    swap b d * swap a b = swap a d * swap d b := by
      ext x
      simp +decide [ Equiv.swap_apply_def ]
      aesop

/-
A transposition σ multiplied by (a b) either cancels or
can be rewritten as (a z) τ where τ fixes a.
-/
lemma move_swap_left {a b : α} (hab : a ≠ b) (σ : Perm α) (hσ : σ.IsSwap) :
    (σ * swap a b = 1) ∨ (∃ z, z ≠ a ∧ ∃ τ, τ.IsSwap ∧ τ a = a ∧ σ * swap a b = swap a z * τ) := by
  rcases hσ with ⟨x, y, hxy, rfl⟩
  -- Check if σ is exactly swap a b (or swap b a)
  by_cases h : swap x y = swap a b
  · left; rw [h, Equiv.swap_mul_self]
  · right
    -- Case: σ involves 'a'
    if ha : x = a ∨ y = a then
      obtain ⟨z, hza, heq⟩ : ∃ z, z ≠ a ∧ swap x y = swap a z := by
        cases ha with
        | inl hxa => subst hxa; exact ⟨y, hxy.symm, rfl⟩
        | inr hya => subst hya; exact ⟨x, hxy, Equiv.swap_comm x y⟩
      rw [heq]
      have hzb : z ≠ b := by intro hb; subst hb; apply h; rw [heq]
      -- Use: swap a z * swap a b = swap a b * swap b z
      refine ⟨b, hab.symm, swap b z, ⟨b, z, by aesop, rfl⟩, ?_, ?_⟩
      · simp [swap_apply_def]; aesop
      · rw [swap_mul_swap_share_left hzb hza]
    -- Case: σ involves 'b' but not 'a'
    else if hb : x = b ∨ y = b then
      obtain ⟨z, hzb, heq⟩ : ∃ z, z ≠ b ∧ swap x y = swap b z := by
        cases hb with
        | inl hxb => subst hxb; exact ⟨y, hxy.symm, rfl⟩
        | inr hyb => subst hyb; exact ⟨x, hxy, Equiv.swap_comm _ _⟩
      rw [heq]
      have hza : z ≠ a := by intro Hz; subst Hz; cases hb <;> grind
      -- Use: swap b z * swap a b = swap a z * swap z b
      refine ⟨z, hza, swap z b, ⟨z, b, hzb, rfl⟩, ?_, ?_⟩
      · simp [swap_apply_def]; aesop
      · rw [swap_mul_swap_share_right hza hzb hab]
    -- Case: σ is disjoint from {a, b}
    else
      push_neg at ha hb
      have hdisj : Disjoint ({a, b} : Set α) {x, y} := by
        rw [Set.disjoint_insert_left, Set.disjoint_singleton_left]
        aesop
      -- Use: swap x y * swap a b = swap a b * swap x y
      refine ⟨b, hab.symm, swap x y, ⟨x, y, hxy, rfl⟩, ?_, ?_⟩
      · simp [swap_apply_def]; aesop
      · rw [swap_mul_swap_comm_of_disjoint hdisj]


/-
Given a list of swaps $M$ and a swap $(a b)$, either the product $M (a b)$ can be
reduced to a shorter list of swaps, or it can be rewritten as $(a z)M'$ where $M'$ fixes $a$.
-/
lemma exists_reduction {α : Type*} [DecidableEq α]
    (M : List (Perm α)) (a b : α) (hab : a ≠ b) (h_swaps : ∀ s ∈ M, s.IsSwap) :
    (∃ M' : List (Perm α), M'.length + 2 = M.length + 1 ∧ (∀ s ∈ M', s.IsSwap) ∧
    M'.prod = (M ++ [swap a b]).prod)
    ∨ (∃ z, z ≠ a ∧ ∃ M' : List (Perm α), (∀ s ∈ M', s.IsSwap ∧ s a = a) ∧
    (M ++ [swap a b]).prod = swap a z * M'.prod) := by
  induction M using List.reverseRecOn generalizing a b
  case nil => right; refine ⟨b, hab.symm, [], by simp, by simp⟩
  case append_singleton L s ih =>
    have hs : s.IsSwap := by simp_all
    have hL_swaps : ∀ x ∈ L, x.IsSwap := by simp_all
    -- Interact s with (swap a b)
    rcases move_swap_left hab s hs with h_cancel | ⟨z, hza, τ, hτ_swap, hτ_fix, h_comm⟩
    -- Case 1: Cancellation (s * swap a b = 1)
    · left
      refine ⟨L, by simp, hL_swaps, ?_⟩
      simp [List.prod_append, h_cancel]
    -- Case 2: Commutation (s * swap a b = swap a z * τ)
    · specialize ih a z hza.symm hL_swaps
      rcases ih with ⟨L', hlen, hops', hprod⟩ | ⟨w, hwa, L', hops', hprod⟩
      -- Subcase 2a: Recursion found a reduction
      · left
        refine ⟨L' ++ [τ], ?_, ?_, ?_⟩
        · simp [List.length_append]; omega
        · intro x hx
          rw [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hops' x hx -- x is in L'
          · exact hτ_swap    -- x is τ
        · simp [List.prod_append, h_comm, mul_assoc, hprod]
      -- Subcase 2b: Recursion found a move
      · right
        refine ⟨w, hwa, L' ++ [τ], ?_, ?_⟩
        · intro x hx
          rw [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hops' x hx
          · exact ⟨hτ_swap, hτ_fix⟩
        · simp only [List.prod_append, List.prod_singleton] at hprod ⊢
          rw [mul_assoc, h_comm, ← mul_assoc, hprod, mul_assoc]


/-
If a list of transpositions multiplies to the identity, its length is even.
-/
theorem even_number_of_swaps_of_identity {α : Type*} [DecidableEq α] [Fintype α]
    (L : List (Perm α)) (hL : ∀ σ ∈ L, σ.IsSwap) (hprod : L.prod = 1) : Even L.length := by
  generalize hn : L.length = n
  induction n using Nat.strong_induction_on generalizing L with
  | h n ih =>
    subst hn
    induction L using List.reverseRecOn with
    | nil => simp
    | append_singleton M s _ =>
      have hs : s.IsSwap := hL s (by simp)
      rcases hs with ⟨a, b, hab, rfl⟩
      have hM_swaps : ∀ x ∈ M, x.IsSwap := fun x hx => hL x (by simp [hx])
      rcases exists_reduction M a b hab hM_swaps with
        ⟨M', hlen, hM'_swaps, h_equiv⟩ | ⟨z, hza, M', hM'_fix, h_equiv⟩
      · rw [← h_equiv] at hprod
        have h_lt : M'.length < (M ++ [swap a b]).length := by
          simp only [List.length_append, List.length_singleton] at hlen ⊢
          omega
        specialize ih M'.length h_lt M' hM'_swaps hprod rfl
        simp only [List.length_append, List.length_singleton]
        rw [← hlen]
        grind
      · rw [h_equiv] at hprod
        have h_apply : (1 : Perm α) a = (swap a z * M'.prod) a := by rw [hprod]
        simp only [Equiv.Perm.coe_one, id_eq, Equiv.Perm.mul_apply] at h_apply
        have h_fix : M'.prod a = a := by
          have helper : ∀ (lst : List (Perm α)), (∀ x ∈ lst, x a = a) → lst.prod a = a := by
            intro lst h
            induction lst with
            | nil => simp
            | cons x xs ih_xs =>
              simp only [List.prod_cons, mul_apply]
              rw [ih_xs (fun y hy => h y (by simp [hy]))]
              exact h x (by simp)
          exact helper M' (fun x hx => (hM'_fix x hx).2)
        -- Logic: a = swap a z (M'.prod a) → a = swap a z a → a = z
        rw [h_fix, swap_apply_left] at h_apply
        -- Contradiction: z ≠ a
        exact (hza h_apply.symm).elim


theorem parity_of_swaps {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) (L1 L2 : List (Perm α)) (hL1 : ∀ s ∈ L1, s.IsSwap) (hL2 : ∀ s ∈ L2, s.IsSwap)
    (h1 : L1.prod = σ) (h2 : L2.prod = σ) : Even L1.length ↔ Even L2.length := by
      have hprod : (L1 ++ L2.reverse).prod = 1 := by
        have hL2_inv : L2.reverse.prod = L2.prod⁻¹ := by
          rw [ List.prod_inv_reverse ];
          have h_inv : ∀ s ∈ L2, s⁻¹ = s := by
            intro s hs; obtain ⟨ a, b, hab, rfl ⟩ := hL2 s hs
            simp
          rw [ List.map_congr_left h_inv ]
          aesop
        aesop
      replace := even_number_of_swaps_of_identity ( L1 ++ L2.reverse ) ?_ hprod
      · grind
      · grind
