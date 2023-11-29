
/-
Copyright (c) 2023 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import tactic data.nat.parity

/-!

# Introduction

This file contains the code referenced in the introductory
chpater of the Master thesis this file belongs to.

-/

namespace intro -- to provide name clashes


-- An example of a proof
lemma my_lemma
  (x y : ℕ) (hx : odd x) (hy : odd y) :
  even (x+y) :=
begin
  -- Click here and look at the infoview
  rw nat.even_iff,
  rw nat.odd_iff at hx hy,
  rw nat.add_mod,
  rw [hx, hy],
  norm_num,
end

#print my_lemma

-- Remainders are computable
#eval 15 % 2 



-- The type of natural numbers
#check nat

-- This is how they're defined
inductive nat
| zero : nat
| succ (n : nat) : nat


open nat


-- Addition of naturals
#check nat.add

def add : nat → nat → nat
| a  zero     := a
| a  (succ b) := succ (add a b)


-- Predecessors of naturals
#check nat.pred

def pred : ℕ → ℕ
| 0     := 0
| (a+1) := a


-- Subtraction of naturals
#check nat.sub

def sub : ℕ → ℕ → ℕ
| a 0     := a
| a (b+1) := pred (sub a b)


#eval 4-5


-- Order of naturals
#check nat.less_than_or_equal

inductive less_than_or_equal (a : ℕ) : ℕ → Prop
| refl : less_than_or_equal a
| step : Π {b}, less_than_or_equal b → less_than_or_equal (b+1)


-- Two examples of proofs
example : 2 ≤ 4 :=
  nat.less_than_or_equal.step (nat.less_than_or_equal.step (@nat.less_than_or_equal.refl 2))

example : 2 ≤ 4 :=
begin
  apply nat.less_than_or_equal.step,
  apply nat.less_than_or_equal.step,
  apply nat.less_than_or_equal.refl,
end

-- A more complex example of a proof
#check nat.mod_le

example (x y : ℕ) : x % y ≤ x :=
  or.elim (lt_or_le x y)
  ((@le_of_eq ℕ _ (x % y) x) ∘ (@nat.mod_eq_of_lt x y))
  (or.elim (nat.eq_zero_or_pos y)
    ( (λ y0 ylex,
          (iff.elim_right ∘ (iff_of_eq ∘ (@congr_arg _ _ y 0 (λ y, x%y ≤ x))))
          (y0)
          (le_of_eq (nat.mod_zero x)))
    )
    ((λ ypos ylex, le_trans (le_of_lt (nat.mod_lt x ypos)) ylex))
    )

-- Now in tactic mode
lemma tac_example_1
  (x y : ℕ) :
  x % y ≤ x :=
begin
  -- Look at the infoview!
  apply or.elim (lt_or_le x y),
  {-- Look at the infoview!
   intro x_lt_y,
   apply le_of_eq,
   apply nat.mod_eq_of_lt,
   -- apply x_lt_y,
   exact x_lt_y,
   },
  {intro y_le_x,
   apply or.elim (nat.eq_zero_or_pos y),
   {intro y_0,
    apply @iff.elim_right _ (x % 0 ≤ x),
    apply iff_of_eq,
    apply @congr_arg _ _ y 0 (λ y, x%y ≤ x),
    exact y_0,
    --rw y_0,
    apply le_of_eq,
    exact nat.mod_zero x,
    },
   {intro y_pos,
    apply le_trans _ y_le_x,
    apply le_of_lt,
    apply nat.mod_lt,
    exact y_pos,
    },
   },
end 

#print tac_example_1


-- A calculatory proof
lemma calculation_1
  (x y : ℚ)
  (h1 : x + y ≤ 1)
  (h2 : x - y ≤ -1) :
  x ≤ 0 :=
begin
  apply @le_of_mul_le_mul_left _ 2 x 0,
  /-
  ⊢ 2 * x ≤ 2 * 0
  ⊢ 0 < 2
  -/
  swap, norm_num, -- ⊢ 2 * x ≤ 2 * 0
  rw [two_mul, mul_zero], -- ⊢ x + x ≤ 0
  rw ← sub_self (y - 1), -- ⊢ x + x ≤ y - 1 - (y - 1)
  rw [sub_eq_add_neg, neg_sub], -- ⊢ x + x ≤ y - 1 + (1 - y)
  apply add_le_add,
  /-
  ⊢ x ≤ y - 1
  ⊢ x ≤ 1 - y
  -/
  {rw sub_eq_add_neg, -- ⊢ x ≤ y + -1
   rw ← sub_le_iff_le_add', -- ⊢ x - y ≤ -1
   exact h2 -- goals accomplished
   },
  {rw sub_eq_add_neg, -- ⊢ x ≤ 1 + -y
   rw ← sub_le_iff_le_add, -- ⊢ x - -y ≤ 1
   rw sub_eq_add_neg, -- ⊢ x + --y ≤ 1
   rw neg_neg, -- ⊢ x + y ≤ 1
   exact h1 -- goals accomplished
   },
end 


-- Solved with a tactic
lemma calculation_2
  (x y : ℚ)
  (h1 : x + y ≤ 1)
  (h2 : x - y ≤ -1) :
  x ≤ 0 :=
begin
  linarith,
end 

-- Compare the proofs
#print calculation_1
#print calculation_2


-- The code for our tactic

meta def destruct_or_helper_try : expr → expr → tactic unit :=
λ P h, 
  do
    match P with
    | `(%%a ∨ %%b) := do
                        {tactic.applyc `or.inl, 
                        tactic.trace "test left directly",
                        tactic.trace "target:",
                        q ← tactic.target,
                        tactic.trace q,
                        tactic.exact h
                        }
                      <|> do
                        {tactic.applyc `or.inr,
                        tactic.trace "test right directly",
                        tactic.trace "target:",
                        q ← tactic.target,
                        tactic.trace q,
                        tactic.exact h
                        }
                      <|> do
                        {tactic.applyc `or.inl,
                         tactic.trace "branch left",
                         destruct_or_helper_try a h
                        }
                      <|> do
                        {tactic.applyc `or.inr,
                         tactic.trace "branch right",
                         destruct_or_helper_try b h
                        }       
    | _ := do {tactic.exact h}
    end

meta def destruct_or_helper : list expr → tactic unit
| [] := do
    {tactic.trace "Failed. Are you trying to show a disjunction ? Do you have one of the certifiers ?",
      tactic.skip}
| (h :: hs) := do
    {tactic.trace "test:",
      tactic.trace h,
      tactic.trace "on target:",
      P ← tactic.target,
      tactic.trace P,
      destruct_or_helper_try P h
      }
    <|> destruct_or_helper hs

meta def destruct_or: tactic unit :=
  do
    {tactic.trace "local context:",
     ctx ← tactic.local_context,
     tactic.trace ctx,
     destruct_or_helper ctx}


variables a b c d : Prop

-- Some successful applications
example (ha : a ∨ b):
  (d ∨ c) ∨ (a ∨ b) :=
  by {destruct_or,
      }

lemma print_me (hb : b) :
  d ∨ ((d ∨ c) ∨ ((a ∨ b) ∨ (a ∨ a))):=
  by {destruct_or,
      }

#print print_me

-- The latter is exactly this proof:
example (hb : b) :
  d ∨ ((d ∨ c) ∨ ((a ∨ b) ∨ (a ∨ a))):=
  by {right,
      right,
      left,
      right,
      exact hb,
      }

-- Can't handle commutativity
example (ha : b ∨ a) :
  (d ∨ c) ∨ (a ∨ b) :=
  by {destruct_or,
      -- Note: the goal is still un-accomplished
      }

end intro