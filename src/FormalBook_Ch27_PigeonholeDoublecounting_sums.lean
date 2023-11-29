/-
Copyright (c) 2023 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import data.finset.basic
import data.finset.card
import tactic

/-!
# Pigeon-hole and double counting : Sums

This file is part of a Master thesis project of formalizing some proofs from
"Proofs from THE BOOK" (5th ed.) by Martin Aigner and Günter M. Ziegler. 

We refer to chapter 27: "Pigeon-hole and double counting".
In this file, we formalize the section "Sums".


## Structure

- `claim` :
      Suppose we are given the n first terms of an integer
      sequence `a`, which need not be pairwise distinct.
      Then there is always a set of consecutive numbers
      k+1,k+2,...,l in [0,n], whose sum of the corresponding
      terms of `a` is a multiple of n.

-/

open finset


/--
A technical lemma for algebraic manipulations with `int.nat_mod`.
-/
lemma tec_mod
  (n : ℕ) (hn : n ≠ 0) (a b :ℤ) (H : int.nat_mod a n = int.nat_mod b n) :
  (int.nat_mod (a-b) n  : ℤ) = 0 :=
begin
  simp only [int.nat_mod] at *,
  apply_fun (λ x, (x : ℤ)) at H,
  have rw_main : ∀ c : ℤ, ↑((c) % ↑n).to_nat = (c) % ↑n :=
    by {intro c,
        apply int.to_nat_of_nonneg,
        apply int.mod_nonneg,
        simp only [ne.def, nat.cast_eq_zero],
        exact hn,
        },
  rw (rw_main a) at H,
  rw (rw_main b) at H,
  rw (rw_main (a-b)),
  rw int.sub_mod,
  rw H,
  simp only [sub_self],
  exact (n : ℤ).zero_mod,
end

#check disjoint

open_locale big_operators

/--
A technical lemma for deleting the first terms of a sum
indexed by `Icc`, all interms of `Icc`.
-/
lemma tec_sum 
  (a : ℕ → ℤ) (b c : ℕ) (h : b < c) :
  (∑ (i : ℕ) in Icc 1 c, a i) - (∑ (i : ℕ) in Icc 1 b, a i)
  = ∑ (i : ℕ) in Icc (b + 1) c, a i :=
begin
  have decompo : Icc 1 c = disj_union (Icc (b+1) c) (Icc 1 b)
                              (by {rw disjoint_iff_inter_eq_empty,
                                   ext y,
                                   simp only [and_imp, finset.not_mem_empty, finset.mem_Icc, not_and, iff_false, finset.mem_inter],
                                   intros yes no nope,
                                   linarith,
                                   }) :=
    by {simp only [finset.disj_union_eq_union],
        --library_search, --fails
        ext x,
        simp only [finset.mem_Icc, finset.mem_union],
        split,
        rintros ⟨x1,xc⟩,
        by_cases q : x≤b,
        right,
        exact ⟨x1,q⟩,
        left,
        split,
        rw nat.add_one_le_iff,
        exact lt_of_not_le q,
        exact xc,
        intro tmp,
        cases tmp with up down,
        split,
        linarith,
        exact up.2,
        split,
        exact down.1,
        linarith,
        },
  rw decompo,
  rw finset.sum_disj_union,
  simp only [eq_self_iff_true, add_tsub_cancel_right],
end


/--
### Claim

Suppose we are given the n first terms of an integer
sequence `a`, which need not be pairwise distinct.
Then there is always a set of consecutive numbers
k+1,k+2,...,l in [0,n], whose sum of the corresponding
terms of `a` is a multiple of n.
-/
lemma claim
  (n : ℕ) (hn : n ≠ 0) (a : ℕ → ℤ) :
  ∃ k l, (k ∈ range (n+1)) ∧ (l ∈ range (n+1)) ∧ (k<l) ∧ 
  (n : ℤ) ∣ (∑ i in (Icc (k+1) l), a i ) :=
begin
  -- The pigeonhole map and the conditions
  let f := (λ m, (int.nat_mod (∑ i in (Icc 1 m), a i ) n)),
  have map_cond : (∀s, s ∈ (range (n+1)) → f s ∈ (range n)) :=
    by {intros m mdef,
        simp only [f, finset.mem_range],
        apply int.nat_mod_lt,
        exact hn,
        },
  have card_cond :((range n).card < (range (n+1)).card) :=
    by {rw [card_range,card_range],
        linarith,
        },
  -- We apply the principle
  obtain ⟨b, bS, c, cS, anb, fbfc⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to card_cond map_cond,
  dsimp [f] at fbfc,
  -- wlog H : b < c with nam, --fails
  apply lt_by_cases b c,
  {intro blc,
   use b, use c,
   split,
   exact bS,
   split,
   exact cS,
   split,
   exact blc,
   -- Some rewrites
   have to_dvd: ((((Icc 1 c).sum a) - ((Icc 1 b).sum a)).nat_mod ↑n : ℤ) = 0 := 
     by {apply tec_mod n hn,
         exact fbfc.symm,
         },
   simp only [int.nat_mod] at to_dvd,
   have : ↑((((Icc 1 c).sum a - (Icc 1 b).sum a) % ↑n).to_nat) = (((Icc 1 c).sum a - (Icc 1 b).sum a) % ↑n) :=
     by {apply int.to_nat_of_nonneg,
         apply int.mod_nonneg,
         simp only [ne.def, nat.cast_eq_zero],
         exact hn,
         },
   rw this at to_dvd,
   clear this,
   rw (tec_sum a b c blc) at to_dvd,
   exact int.dvd_of_mod_eq_zero to_dvd,
  },
  -- The false case
  {intro nope,
   exfalso,
   exact anb nope,
  },
  -- swap b and c, proceed as in the first bloc
  {intro blc,
   use c, use b,
   split,
   exact cS,
   split,
   exact bS,
   split,
   exact blc,
   -- Some rewrites
   have to_dvd: ((((Icc 1 b).sum a) - ((Icc 1 c).sum a)).nat_mod ↑n : ℤ) = 0 := 
     by {apply tec_mod n hn,
         exact fbfc,
         },
   simp only [int.nat_mod] at to_dvd,
   have : ↑((((Icc 1 b).sum a - (Icc 1 c).sum a) % ↑n).to_nat) = (((Icc 1 b).sum a - (Icc 1 c).sum a) % ↑n) :=
     by {apply int.to_nat_of_nonneg,
         apply int.mod_nonneg,
         simp only [ne.def, nat.cast_eq_zero],
         exact hn,
         },
   rw this at to_dvd,
   clear this,
   rw (tec_sum a c b blc) at to_dvd,
   exact int.dvd_of_mod_eq_zero to_dvd,
  },
end




