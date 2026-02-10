import Mathlib.Tactic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Data.List.Induction

open Equiv Perm

-- Here the permutation group is defined as (Perm α), where α can be any set
-- If we take α = Fin n, we will get Sₙ

variable {α : Type*} [DecidableEq α]

lemma swap_mul_swap_comm_of_disjoint {a b c d : α}
    (h : Disjoint ({a, b} : Set α) {c, d}) :
    swap a b * swap c d = swap c d * swap a b := by
      ext x
      simp +decide [ Equiv.swap_apply_def ]
      aesop

lemma swap_mul_swap_share_left {a b c : α} (hcb : c ≠ b) (hca : c ≠ a) :
    swap a c * swap a b = swap a b * swap b c := by
      ext x
      by_cases h : x = a <;>
      by_cases h' : x = b <;>
      by_cases h'' : x = c <;>
      simp +decide [ *, Equiv.swap_apply_def ]
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
A transposition $\sigma$ multiplied by $(a\,b)$ either cancels or
can be rewritten as $(a\,z)\tau$ where $\tau$ fixes $a$.
-/
lemma move_swap_left {a b : α} (hab : a ≠ b) (σ : Perm α) (hσ : σ.IsSwap) :
    (σ * swap a b = 1) ∨ (∃ z, z ≠ a ∧ ∃ τ, τ.IsSwap ∧ τ a = a ∧ σ * swap a b = swap a z * τ) := by
      rcases hσ with ⟨ x, y, hxy ⟩;
      by_cases h : x = a ∨ x = b <;>
      by_cases h' : y = a ∨ y = b <;>
      simp_all +decide only [ne_eq];
      · rcases h with ( rfl | rfl ) <;>
        rcases h' with ( rfl | rfl ) <;>
        simp_all +decide [ Equiv.swap_comm ];
      · rcases h with ( rfl | rfl ) <;>
        simp_all +decide only [Perm.ext_iff, not_or, coe_mul, Function.comp_apply, coe_one, id_eq];
        · refine' Or.inr ⟨ b, _, Equiv.swap y b, _, _, _ ⟩ <;>
          simp_all only [swap_apply_def, ↓reduceIte];
          · tauto;
          · exact ⟨ y, b, by aesop ⟩;
          · grind;
        · refine' Or.inr ⟨ y, _, Equiv.swap x y, _, _, _ ⟩ <;>
          simp_all +decide only [swap_apply_def]
          · exact ⟨ x, y, by aesop ⟩;
          · grind;
          · grind;
      · rcases h' with ( rfl | rfl ) <;>
        simp_all +decide [ Equiv.Perm.ext_iff ];
        · refine' Or.inr ⟨ b, _, Equiv.swap x b, _, _, _ ⟩ <;>
          simp_all only [swap_apply_def];
          · grind;
          · exact ⟨ x, b, by aesop ⟩;
          · grind;
          · grind;
        · refine' Or.inr ⟨ x, _, Equiv.swap y x, _, _, _ ⟩ <;>
          simp_all +decide only [swap_apply_def];
          · exact ⟨ y, x, by aesop ⟩;
          · grind;
          · grind;
      · refine' Or.inr ⟨ b, by tauto, Equiv.swap x y, _, _, _ ⟩ <;>
        simp_all only [Perm.ext_iff, swap_apply_def, not_or, coe_mul, Function.comp_apply]
        · exact ⟨ x, y, by aesop ⟩;
        · grind;
        · grind

/-
Given a list of swaps $M$ and a swap $(a\,b)$, either the product $M(a\,b)$ can be
reduced to a shorter list of swaps, or it can be rewritten as $(a\,z)M'$ where $M'$ fixes $a$.
-/
lemma exists_reduction {α : Type*} [DecidableEq α]
(M : List (Perm α)) (a b : α) (hab : a ≠ b) (h_swaps : ∀ s ∈ M, s.IsSwap) :
(∃ M' : List (Perm α), M'.length + 2 = M.length + 1 ∧ (∀ s ∈ M', s.IsSwap) ∧ M'.prod = (M ++ [swap a b]).prod)
∨ (∃ z, z ≠ a ∧ ∃ M' : List (Perm α), (∀ s ∈ M', s.IsSwap ∧ s a = a) ∧ (M ++ [swap a b]).prod = swap a z * M'.prod) := by
      induction' M using List.reverseRecOn with M s ih generalizing a b;
      · refine' Or.inr ⟨ b, hab.symm, [ ], _, _ ⟩ <;>
        simp [ hab.symm ]
      · have h_move_swap_left : (s * swap a b = 1) ∨
            (∃ z, z ≠ a ∧ ∃ τ, τ.IsSwap ∧ τ a = a ∧ s * swap a b = swap a z * τ) := by
          apply move_swap_left hab s (h_swaps s (by simp));
        rcases h_move_swap_left with ( h | ⟨ z, hz, τ, hτ, hτa, h ⟩ );
        · simp_all +decide [ mul_assoc, List.prod_append ];
          exact Or.inl ⟨ M, rfl, fun s hs => h_swaps s ( Or.inl hs ), rfl ⟩;
        · specialize ih a z;
          simp_all +decide [ List.prod_append, mul_assoc ];
          rcases ih ( Ne.symm hz ) with ( ⟨ M', hM'₁, hM'₂, hM'₃ ⟩ | ⟨ w, hw, M', hM'₁, hM'₂ ⟩ );
          · refine' Or.inl ⟨ M' ++ [ τ ], _, _, _ ⟩ <;> simp_all +decide [ ← mul_assoc ];
            rintro s ( hs | rfl ) <;> [ exact hM'₂ s hs; exact hτ ];
          · refine' Or.inr ⟨ w, hw, M' ++ [ τ ], _, _ ⟩ <;>
            simp_all +decide [ mul_assoc ]
            · rintro s ( hs | rfl ) <;> [ exact hM'₁ s hs; exact ⟨ hτ, hτa ⟩ ];
            · rw [ ← mul_assoc, hM'₂, mul_assoc ]

/-
If a list of transpositions multiplies to the identity, its length is even.
-/
theorem even_number_of_swaps_of_identity {α : Type*} [DecidableEq α] [Fintype α]
    (L : List (Perm α)) (hL : ∀ σ ∈ L, σ.IsSwap) (hprod : L.prod = 1) :
    Even L.length := by
      -- In the base case, $L$ is empty, so its length is zero.
      by_cases h_empty : L = [];
      · simp +decide [ h_empty ];
      · -- By induction on the length of $L$, we can show that if the
        -- length is odd, then the product cannot be the identity.
        induction' hn : L.length using Nat.strong_induction_on with n ih generalizing L;
        -- Let's denote the last element of $L$ as $\tau$.
        obtain ⟨M, τ, hM, hτ, hL_eq⟩ :
        ∃ M : List (Equiv.Perm α), ∃ τ : Equiv.Perm α, L = M ++ [τ] ∧ τ.IsSwap := by
          exact ⟨ L.dropLast, L.getLast h_empty,
          by rw [ List.dropLast_append_getLast h_empty ], hL _ ( List.getLast_mem h_empty ) ⟩
        -- By `exists_reduction`, either there exists a shorter list $M'$ with
        -- length $n - 1$ such that $M'.prod = L.prod$,
        -- or there exists $z \ne hτ$ and $M'$ such that $M'.prod = (hτ \, z) \cdot L.prod$.
        obtain (hM' | ⟨z, hz, M', hM'_prod⟩) :
        (∃ M' : List (Equiv.Perm α), M'.length + 2 = M.length + 1 ∧
        (∀ s ∈ M', s.IsSwap) ∧ M'.prod = (M ++ [τ]).prod) ∨ (∃ z, z ≠ hτ ∧
        ∃ M' : List (Equiv.Perm α), (∀ s ∈ M', s.IsSwap ∧ s hτ = hτ) ∧ (M ++ [τ]).prod = swap hτ z * M'.prod) := by
          have h_reduction : ∀ (M : List (Equiv.Perm α)) (a b : α), a ≠ b → (∀ s ∈ M, s.IsSwap) →
          (∃ M' : List (Equiv.Perm α), M'.length + 2 = M.length + 1 ∧ (∀ s ∈ M', s.IsSwap) ∧
          M'.prod = (M ++ [swap a b]).prod) ∨ (∃ z, z ≠ a ∧
          ∃ M' : List (Equiv.Perm α), (∀ s ∈ M', s.IsSwap ∧ s a = a) ∧ (M ++ [swap a b]).prod
          = swap a z * M'.prod) := by
            exact?;
          rcases hL_eq with ⟨ y, hy, rfl ⟩
          simpa using h_reduction M hτ y hy ( fun s hs => hL s ( hM.symm ▸ List.mem_append_left _ hs ) ) ;
        · obtain ⟨ M', hM₁, hM₂, hM₃ ⟩ := hM';
          simp_all +decide [ List.prod_append ];
          specialize ih ( M'.length ) ( by linarith ) M' hM₂ hM₃;
          grind;
        · -- Apply both sides of the equation to $hτ$.
          have h_apply : (Equiv.swap hτ z * M'.prod) hτ = hτ := by
            simp_all +decide [ Equiv.Perm.ext_iff ];
          -- Since every element of $M'$ fixes $hτ$, we have $M'.prod hτ = hτ$.
          have hM'_prod_hτ : M'.prod hτ = hτ := by
            have hM'_prod_hτ : ∀ s ∈ M', s hτ = hτ := by
              exact fun s hs => hM'_prod.1 s hs |>.2;
            have hM'_prod_hτ : ∀ (l : List (Equiv.Perm α)), (∀ s ∈ l, s hτ = hτ) → l.prod hτ = hτ := by
              intro l hl; induction l <;> simp_all +decide [ Equiv.Perm.mul_apply ] ;
            exact hM'_prod_hτ M' ‹_›;
          rw [ Equiv.Perm.mul_apply ] at h_apply ; aesop


theorem parity_of_swaps {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) (L1 L2 : List (Perm α))
    (hL1 : ∀ s ∈ L1, s.IsSwap) (hL2 : ∀ s ∈ L2, s.IsSwap)
    (h1 : L1.prod = σ) (h2 : L2.prod = σ) :
    Even L1.length ↔ Even L2.length := by
      have hprod : (L1 ++ L2.reverse).prod = 1 := by
        -- Since each element in $L_2$ is a swap, it is its own inverse.
        have hL2_inv : L2.reverse.prod = L2.prod⁻¹ := by
          rw [ List.prod_inv_reverse ];
          have h_inv : ∀ s ∈ L2, s⁻¹ = s := by
            intro s hs; obtain ⟨ a, b, hab, rfl ⟩ := hL2 s hs
            simp
          rw [ List.map_congr_left h_inv ]
          aesop
        aesop
      replace := even_number_of_swaps_of_identity ( L1 ++ L2.reverse ) ?_ hprod
      simp_all +decide [ List.length_reverse ]
      · grind
      · grind
