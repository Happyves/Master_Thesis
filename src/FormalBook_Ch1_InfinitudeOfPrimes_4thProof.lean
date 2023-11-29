
/-
Copyright (c) 2023 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import data.finset.card
import data.finset.sort
import algebra.geom_sum
import data.nat.prime_norm_num
import data.nat.prime
import algebra.big_operators.basic
import algebra.big_operators.order
import algebra.big_operators.associated
import tactic

-- Imports not essential to the file, only used for
-- allusions to alternative formalizations.  
import data.nat.nth
import data.nat.factorization.basic
import data.fintype.big_operators


/-!
# Six proofs of the inﬁnity of primes : 4th proof

This file is part of a Master thesis project of formalizing some proofs from
"Proofs from THE BOOK" (5th ed.) by Martin Aigner and Günter M. Ziegler. 

We refer to chapter 1: "Six proofs of the inﬁnity of primes".
In this file, we formalize "Fourth proof", the 4th of the six proofs.


## Structure

- `fourth_proof` :
      The fourth proof of infinitude of primes.
      It's based on the divergence of the harmonic series.
- `π` :
      The prime counting function
- `the_great_merger` :
      We lower bound the prime counting function by the
      harmonic series. This is the central argument for
      showing infinitude of primes.
- `order_the_prod` :
      Ordering the product `∏ (p/(p-1) : ℚ)` according
      to the order of increasing primes
- `kth_prime_among_bound` :
      Shows that the kth prime is ≥ k+1
- `prod_ordered_primes_bound` :
      Lower-bounds (π n)+1 by the ordered product of primes
- `prod_sum_bound` :
      Lower-bounds the product of primes by the product
      of geometric sums over the primes.
- `the_great_split_part_1` :
      First step in linking the hamronic series to the
      produc of geometric sums:
      distributing the product of sums.
- `the_great_split_part_2` :
      Second step in linking the hamronic series to the
      produc of geometric sums:
      lower-bounding the distributing the product of sums
      by the sum on the subset obtained by filtering out
      the terms who's value isn a 1/k for k∈[n].
- `the_great_split_part_3` :
      Final step in linking the hamronic series to the
      produc of geometric sums:
      upper-bound the harmonic sum with the filtered
      sum of products.
- `quick_prime_decompo` :
      A home-made version of decomposition into primes.
- `harmonic_unbounded` :
      A home-made proof that the harmonic series is unbounded.
-/


open finset

open_locale big_operators



/-- The set of primes `≤ n`-/
def primes_up_to (n : ℕ) : finset ℕ :=
  (range (n+1)).filter (λ p, nat.prime p)

/-- Counts the number of primes `≤ n`-/
def π (n : ℕ) : ℕ :=
  ((range (n+1)).filter (λ p, nat.prime p)).card

-- They are computable
#eval π 10 
#eval π 100000
  -- first 0 where this made my laptop take a second,
  -- next 0 causes a timeout

#eval primes_up_to 10
#eval primes_up_to 100000

-- I later found out about:
#check nat.nth
--However, it's not computable. Making the following
-- and #eval will fail
#check nat.nth nat.prime 3

/--
A function that takes as input `n`, `k` and a proof that
`k < (π n)`, and returns the `k`th prime among the first
`n+1` numbers 0,1,...,n.

We start the counting at 0 for `k`.
-/
def kth_prime_among (n k: ℕ) (h : k < (π n)) := 
  list.nth_le (finset.sort (≤) ((range (n+1)).filter (λ p, nat.prime p))) k 
  (by {rw [π] at h, simp only [finset.length_sort], exact h, })

/-
For some functions, specific value equalities can be
shown with refl, dec_trivial, or norm_num.
For example:
-/ 
def funtest (x : nat) : ℕ  :=  2*x
#eval funtest 2
example : funtest 2 = 4 := by {refl,}
/-
For more complicated ones, proofs are necessary. 
The following proof is due to Bhavik Mehta. 
-/
lemma thanks_Bhavik : π  10 = 4 :=
begin 
  rw [π ],
  iterate 11 {
    rw [finset.range_succ, finset.filter_insert, apply_ite finset.card,
      finset.card_insert_of_not_mem],
    swap, { simp },
    norm_num1,
    simp only [if_true, if_false],
  },
  rw [finset.range_zero, finset.filter_empty, finset.card_empty],
  norm_num1,
end

-- This computes the 2nd prime in 0,1,...10
#eval kth_prime_among 10 1 (by {rw thanks_Bhavik, norm_num,})
-- This computes the 4th prime in 0,1,...10
#eval kth_prime_among 10 3 (by {rw thanks_Bhavik, norm_num,})

/--
A function that takes as input `n`, `p` and a proof that
`p` is a prime `≤ n` in the language of finsets,
and returns the rank/order of the prime `p`,
in the form of a number of type ` fin (π n)`.

We start the counting at 0 for the rank/order.
-/
def prime_rank_among (n p: ℕ) (h : p ∈ ((range (n+1)).filter (λ q, nat.prime q))) : fin (π n) :=
  ⟨ list.index_of p (finset.sort (≤) (((range (n+1)).filter (λ q, nat.prime q)))),
    by {simp only [π], rw ← finset.length_sort has_le.le, 
        rw list.index_of_lt_length, rw finset.mem_sort, exact h,}⟩ 

-- This computes the rank of the prime 5 in 0,1,...10,
-- which is 3.
#eval prime_rank_among 10 5 (by {norm_num,})

-- This computes the rank of the prime 5 in 0,1,...10,
-- which is 4.
#eval prime_rank_among 10 7 (by {norm_num,})


/-- `kth_prime_among` is a left inverse to `prime_rank_among` -/
lemma order_tec_1
  (n p: ℕ) (h :p ∈ ((range (n+1)).filter (λ q, nat.prime q))):
  kth_prime_among n (prime_rank_among n p h).val (prime_rank_among n p h).prop = p :=
by {simp [kth_prime_among, prime_rank_among],}

/-- `kth_prime_among n k h` is a prime `≤ n` -/
lemma kth_prime_among_makes_sense
  (n k: ℕ) (h : k < (π n)) :
  (kth_prime_among n k h) ∈ (range (n+1)).filter nat.prime :=
begin
  rw [kth_prime_among],
  rw ← finset.mem_to_list,
  have : list.perm  (finset.sort (≤) (filter nat.prime (range (n + 1)))) (filter nat.prime (range (n + 1))).to_list :=
    by {exact sort_perm_to_list has_le.le (filter nat.prime (range (n + 1)))},
  rw ← (list.perm.mem_iff this),
  apply list.nth_le_mem,
end

/-- `kth_prime_among n k h` is a prime `≤ n`, explicit version -/
lemma kth_prime_among_makes_sense'
  (n k: ℕ) (h : k < (π n)) :
  (kth_prime_among n k h < n+1) ∧ (nat.prime (kth_prime_among n k h)) :=
begin
  have := kth_prime_among_makes_sense n k h,
  rw mem_filter at this,
  rwa mem_range at this,
end



/-- `kth_prime_among` is a right inverse to `prime_rank_among` -/
lemma order_tec_2
  (n k: ℕ) (h : k < (π n)) :
  prime_rank_among n (kth_prime_among n k h) (kth_prime_among_makes_sense n k h) = ⟨k,h⟩ :=
by {simp [kth_prime_among, prime_rank_among],}

/--
Expressing the set of primes `≤ n` as the image of
0,1,...,(π n)-1 under `kth_prime_among`.
-/
lemma tec_order_set { n : ℕ } :
  ((range (n+1)).filter (λ p, nat.prime p)) =
  image (λ k : fin (π n), kth_prime_among n k.val k.prop) (univ : finset (fin (π n))) :=
begin
  ext x,
  split,
  {intro xfil,
   rw mem_image,
   use (prime_rank_among n x xfil),
   simp only [true_and, finset.mem_univ, fin.val_eq_coe],
   apply order_tec_1,
  },
  {intro xim,
   simp? at xim,
   cases xim with y ydef,
   rw ←ydef,
   apply kth_prime_among_makes_sense,
  },
end

/-- 
Ordering `∏ (p/(p-1) : ℚ)` according to the order of primes,
using `kth_prime_among`. 
-/
lemma order_the_prod { n : ℕ } :
  ∏ p in ((range (n+1)).filter (λ p, nat.prime p)), (p/(p-1) : ℚ) =
  ∏ k in (univ : finset (fin (π n))), ((kth_prime_among n k.val k.prop)/((kth_prime_among n k.val k.prop)-1) : ℚ)
  :=
begin
  rw tec_order_set,
  apply prod_image,
  simp,
  intros x y eq,
  rw [kth_prime_among] at eq,
  apply fin.eq_of_veq,
  have : list.nodup (finset.sort (≤) ((range (n+1)).filter (λ p, nat.prime p))) :=
    by {exact sort_nodup has_le.le (filter (λ (p : ℕ), nat.prime p) (range (n + 1)))},
  apply list.nodup_iff_nth_le_inj.mp this,
  exact eq,
end

-- We didn't end up needing the following
/--
`π` is an increasing function that increases either by 0
or by one for each successive number `n`.
-/
lemma π_increase {n : ℕ} :
  (π n ≤ π n.succ) ∧ (π n.succ ≤ (π n) +1) :=
begin
  simp [π],
  split,
  {apply card_le_of_subset,
   apply filter_subset_filter,
   simp only [finset.range_subset, le_add_iff_nonneg_right, zero_le'],
   },
  {nth_rewrite 0 range_succ,
   rw filter_insert,
   split_ifs,
   {rw card_insert_of_not_mem _,
    simp only [finset.not_mem_range_self, not_false_iff, finset.mem_filter, false_and],
    },
   {apply nat.le_succ,},
  },
end

-- We now derive some list lemmata.
-- `list_stuff_0` and `list_stuff_1` didn't turn out to be
-- useful to us and my be skipped. We kept them in here as
-- they may be mathlib material. 

/-- If `a :: la` is a prefix of `b :: lb`, then `a = b`-/
lemma list_stuff_0
  (a b: ℕ) (la lb: list ℕ) (h: a :: la <+: b :: lb) :
  a = b :=
    by {simp [list.is_prefix] at h, exact h.1,}

/--
If `la` is a prefix of `lb`, and `k` is smaller then
the length of `k`, the the `k`th element of lists
`la` and `lb` coincide.
-/
lemma list_stuff_1
  (k : nat) (la lb : list ℕ) (hp : la <+: lb) (hl : k < la.length): 
  la.nth_le k (by {assumption}) =
  lb.nth_le k (by {apply lt_of_lt_of_le hl,
                   rw [list.is_prefix] at hp,
                   cases hp with t teq,
                   rw ← teq,
                   simp only [list.length_append, le_add_iff_nonneg_right, zero_le'],
                   }) :=
begin
  revert la lb,
  induction k with k ih,
  intros la lb h H,
  cases la with a la',
  exfalso, simp at H, exact H,
  cases lb with b lb',
  exfalso, simp at h, exact h,
  simp,
  exact list_stuff_0 a b la' lb' h,
  intros la lb h H,
  cases la with a la',
  exfalso, simp at H, exact H,
  cases lb with b lb',
  exfalso, simp at h, exact h,
  simp,
  apply ih,
  simp [list.is_prefix] at *,
  exact h.2,
end

/--
If a list `l` is sorted, then for an index `k` such that
`k+1` is less then the lists length, the `k`th element of
list `l` will be `≤`  then the `k+1`th
-/
lemma list_stuff_2
  (l : list nat) ( hl : list.sorted (≤) l) (k : nat) (hk : k.succ < l.length) :
  l.nth_le k (by {rw nat.succ_eq_add_one at hk, linarith,}) ≤ l.nth_le k.succ hk :=
begin
  revert k,
  induction l with a l ih,
  {intros k hk, exfalso, simp at hk, exact hk,},
  intros k hk,
  rw list.sorted_cons at hl,
  cases k,
  simp, apply hl.1, apply list.nth_le_mem,
  simp, apply ih, exact hl.2,
end

/--
If a list `l` has no duplicates, then for an index `k`
such that `k+1` is less then the lists length, the `k`th
element of list `l` will be different from the `k+1`th
-/
lemma list_stuff_3
  (l : list nat) ( hl : list.nodup l) (k : nat) (hk : k.succ < l.length) :
  l.nth_le k (by {rw nat.succ_eq_add_one at hk, linarith,}) ≠ l.nth_le k.succ hk :=
begin
    revert k,
    induction l with a l ih,
    {intros k hk, simp at hk, exact false.elim hk,},
    intros k hk,
    rw list.nodup_cons at hl,
    cases k,
    simp, intro con, rw con at hl, apply hl.1, apply list.nth_le_mem,
    simp, apply ih, exact hl.2,
end

/-- The `kth_prime_among` function increases by at leat 1 for successive indices.  -/
lemma kth_prime_among_increase
  (n k: ℕ) (h : k.succ < (π n)) :
  kth_prime_among n k (by {rw nat.succ_eq_add_one at h, linarith,}) + 1 ≤  kth_prime_among n k.succ h :=
begin
  simp [kth_prime_among],
  rw nat.add_one_le_iff,
  apply lt_of_le_of_ne,
  {apply list_stuff_2,
   exact finset.sort_sorted (≤) (filter nat.prime (range (n + 1))),},
  {apply list_stuff_3,
   exact finset.sort_nodup (≤) (filter nat.prime (range (n + 1))),},
end

/-- The lower bound on the `k`th prime: `k+2 ≤ kth_prime_among n k` -/
lemma kth_prime_among_bound
  (n k: ℕ) (h : k < (π n)) :
  k+2 ≤ kth_prime_among n k h :=
begin
  induction k with k ih,
  {rw zero_add,
    apply nat.prime.two_le,
    exact (kth_prime_among_makes_sense' n 0 h).2,
    },
  {have : _ := kth_prime_among_increase n k h,
   apply le_trans _ this,
   simp_rw nat.succ_eq_add_one k,
   linarith [ih (show k < π n,
      by {rw nat.succ_eq_add_one at h,
          apply lt_trans _ h,
          exact lt_add_one k,})],
  },
end

/-- We bound the ordered product of primes using the bound `kth_prime_among_bound`-/
lemma prod_ordered_primes_bound_pre (n : ℕ):
  ∏ k in (univ : finset (fin (π n))), ((kth_prime_among n k.val k.prop)/((kth_prime_among n k.val k.prop)-1) : ℚ) 
  ≤ ∏ k in (univ : finset (fin (π n))), ((k.val +2)/(k.val +1) : ℚ)  :=
begin
  have useful_tec : ∀(k : fin (π n)), nat.prime (kth_prime_among n k.val k.prop) := 
    by {intro k,
        exact (kth_prime_among_makes_sense' n k.val k.prop).2},
  apply prod_le_prod,
  {intros k kdef,
   apply div_nonneg,
   exact @nat.cast_nonneg ℚ _ (kth_prime_among n k.val k.prop),
   rw le_sub_iff_add_le, rw zero_add, simp only [nat.one_le_cast, fin.val_eq_coe],
   exact le_of_lt (nat.prime.one_lt (useful_tec k)),
   -- `nat.prime.one_le` doesn't exist
  },
  {intros i idef,
   -- We bring both sides in form (1 + 1/(1 ± x)) to makes comparison easier
  have : ((kth_prime_among n i.val i.prop)/((kth_prime_among n i.val i.prop)-1) : ℚ)
          = 1 + (1/((kth_prime_among n i.val i.prop)-1) : ℚ) :=
    by {have := sub_add_cancel ((kth_prime_among n i.val i.prop) : ℚ) (1 : ℚ ),
        nth_rewrite 0 ←this, clear this,
        rw add_div,
        simp only [one_div, fin.val_eq_coe, add_left_inj],
        apply div_self,
        intro con,
        rw sub_eq_iff_eq_add at con,
        rw zero_add at con,
        apply (nat.prime.ne_one (useful_tec i)),
        rw ← (@nat.cast_inj ℚ _ _ _ _),
        apply con,
       },
  rw this, clear this,
  have : ((i.val +2)/(i.val +1) : ℚ) = 1 + 1/(( i.val +1) : ℚ) :=
    by {rw (show (2 : ℚ) = 1 + 1, by {norm_num}),
        rw ← add_assoc,
        rw add_div,
        simp only [one_div, fin.val_eq_coe, add_left_inj],
        apply div_self,
        exact nat.cast_add_one_ne_zero i.val,
        },
  rw this, clear this,
  simp only [one_div, fin.val_eq_coe, add_le_add_iff_left],
  rw inv_le_inv,
  -- We may now make use of `kth_prime_among_bound`
  {rw le_sub_iff_add_le, rw add_assoc, rw ← (show (2 : ℚ) = 1 + 1, by {norm_num}),
   have coe_pull : ((i : ℕ)  +2 : ℚ) = ↑(i.val + 2) :=
     by {simp only [algebra_map.coe_one, fin.val_eq_coe, add_left_inj, nat.cast_bit0, eq_self_iff_true, nat.cast_inj, nat.cast_add],},
   rw coe_pull,
   rw nat.cast_le,
   apply kth_prime_among_bound n i.val i.prop,
  },
  {rw lt_sub_iff_add_lt,
   rw zero_add,
   simp only [nat.one_lt_cast],
   exact nat.prime.one_lt (useful_tec i),
  },
  {rw ← nat.cast_add_one,
  have coe_pull: ↑0 = (0 : ℚ) :=
    by {simp only [algebra_map.coe_zero, eq_self_iff_true],},
  rw ← coe_pull,
  rw nat.cast_lt,
  apply nat.succ_pos,
  },
  },
end



/-
A technical lemma about the fin-ℕ relation in products. 
This is close to `fin.prod_univ_eq_prod_range`,
but seems to behave differently, as can be seen in
`prod_ordered_primes_bound`.
-/
lemma prod_fin_range (f : ℕ → ℚ) (n : ℕ):
  ∏ k in (univ : finset (fin n)), f k.val = ∏ k in range n, f k :=
begin
  --library_search, --fails
  apply prod_bij (λ a : fin n, λ auniv : a ∈ (univ : finset ( fin n)), a.val),
  -- map
  intros a ha, simp only [fin.is_lt, fin.val_eq_coe, finset.mem_range],
  -- equality
  intros a ha, simp only [fin.val_eq_coe, eq_self_iff_true],
  -- injectivity
  intros a b ha hb, dsimp, rw [← fin.val_eq_coe, ← fin.val_eq_coe], exact (fin.eq_iff_veq a b).mpr,
  --surjectivity
  intros b bdef, rw mem_range at bdef,
  use ⟨b,bdef⟩,
  have ha :  (⟨b,bdef⟩ : fin n) ∈ univ := by {refine mem_univ ⟨b, bdef⟩} ,
  use ha,
end

#check fin.prod_univ_eq_prod_range
  -- I didn't know about this one, before writing the proof
  -- to the previous result, as you can guess from the failed
  -- library search.


#check prod_range_div
  -- Requires a commutative group, which (ℚ,×) isn't 

/--
A technical lemma for telescoping, without having to
cast to ℚ* so as to be able to use `prod_range_div`
-/
lemma prod_range_telescope
  (f : ℕ → ℚ) (n : ℕ) (h : ∀ n : ℕ, f n ≠ 0) :
  ∏ k in range n, (f k.succ)/(f k) = (f n)/(f 0) :=
begin
  --library_search, --fails
  apply prod_range_induction,
  {apply div_self,
   exact h 0,},
  {intro n,
   rw mul_comm,
   rw div_mul_div_cancel,
   exact h n,},
end

/-- Upper-bounds the ordered product of primes by the prime counting function-/
lemma prod_ordered_primes_bound (n : ℕ):
  ∏ k in (univ : finset (fin (π n))), ((kth_prime_among n k.val k.prop)/((kth_prime_among n k.val k.prop)-1) : ℚ) 
  ≤ (π n) + 1  :=
begin
  apply le_of_le_of_eq (prod_ordered_primes_bound_pre n),
  rw prod_fin_range (λ k, ((k+2)/(k+1) : ℚ)) (π n),
  -- simp_rw fin.val_eq_coe,
  --rw fin.prod_univ_eq_prod_range (λ k, ((k+2)/(k+1) : ℚ)) (π n),
    --alternative to the previous line
  dsimp,
  simp_rw [(show (2 : ℚ ) = 1 + 1, by {norm_num,}), ← add_assoc],
  --rw prod_range_div (λ x, (x + 1 : ℚ)) (π n),
    -- telescoping with this would require working in ℚ*
    -- as a multiplicative group, which requires casting 
  simp_rw [(show ∀ x : ℕ, (x : ℚ ) + 1 = (x.succ : ℚ ), by {norm_num,})],
  rw prod_range_telescope (λ x, (x.succ : ℚ)),
  {simp?,},
  {intro m,
   dsimp,
   intro con,
   have : (0 : ℚ) = ((0 : ℕ) : ℚ) := by {simp,},
   rw this at con,
   rw nat.cast_inj at con,
   exact (nat.succ_ne_zero m) con,
  },
end


#check prod_attach
  --This serves as a good example for library search inflexibility
lemma prod_set_attach
  {α : Type} [comm_monoid α] (f : ℕ → α) (s : finset ℕ) : 
  ∏ k in s.attach, f k.val = ∏ k in s, f k :=
by {--library_search, --fails
    apply prod_bij (λ x : {x // x ∈ s}, λ h : x ∈ s.attach , x.val),
    simp,
    simp,
    simp,
    simp,}

/-- 
Rewrites the product of primes in a form suitable
to introduce sums of geometric series.
-/
lemma rw_the_prod {n : ℕ} : 
  ∏ p in ((range (n+1)).filter (λ p, nat.prime p)), (p/(p-1) : ℚ) =  ∏ p in ((range (n+1)).filter (λ p, nat.prime p)), (1/(1-(1/p)) : ℚ) :=
begin 
  rw ← prod_attach,
  nth_rewrite 1 ← prod_attach,
  congr, apply funext, rintro p,
  have : (1 : ℚ) - 1/↑(↑p) = (↑(↑p) - 1)/↑(↑p) :=
    by {rw sub_div, rw div_self,
        intro con,
        have : (0 : ℚ) = ((0 : ℕ) : ℚ) := by {simp,},
        rw this at con, clear this,
        rw nat.cast_inj at con,
        have := p.prop, rw mem_filter at this,
        exact (nat.prime.ne_zero this.2) con,
        },
  rw this,
  simp only [eq_self_iff_true, one_div_div],
end


-- This lemma isn't actually used
lemma geom_sum_Icc_le_one_div_of_lt_one
  {α : Type} [_inst_1 : linear_ordered_field α] {x : α} :
  0 ≤ x → x < 1 → ∀ {n : ℕ}, ∑ (i : ℕ) in Icc 1 n, x ^ i ≤ 1 / (1 - x) :=
by {intros xpos xleone n,
    have : Icc 1 n = Ico 1 (n+1) :=
      by {--library_search, -- → todo
          ext x, split,
          intros icc, rw mem_Icc at icc, rw mem_Ico, split, linarith, linarith,
          intros ico, rw mem_Ico at ico, rw mem_Icc, split, linarith, linarith,},
     rw this,
     apply le_trans (geom_sum_Ico_le_of_lt_one xpos xleone),
     apply div_le_div,
     exact zero_le_one,
     rw pow_one, exact le_of_lt xleone,
     linarith,
     apply le_refl,}

/-- An isolated step of for `prod_sum_bound` -/
lemma prod_sum_bound_pre
  {n p : ℕ} (hp : p ∈ ((range (n+1)).filter (λ p, nat.prime p)) ): 
  ∑ k in Ico 0 (n+1), ((1/p)^k : ℚ) ≤ 1/(1-(1/p)) :=
begin
  nth_rewrite 0 [← (pow_zero (1/p : ℚ))],
  apply geom_sum_Ico_le_of_lt_one,
  {apply div_nonneg,
   exact zero_le_one,
   rw [(show ((0 : ℚ) = ((0 : ℕ) : ℚ)), by {simp,})],
   rw nat.cast_le,
   exact zero_le p,
  },
  {rw mem_filter at hp,
    -- If we don't rw here, we'll have to rw multiple times,
    -- once for each subgoal
   rw div_lt_iff,
   rw one_mul,
   rw [(show ((1 : ℚ) = ((1 : ℕ) : ℚ)), by {simp,})],
   rw nat.cast_lt,
   exact nat.prime.one_lt hp.2,
   rw [(show ((0 : ℚ) = ((0 : ℕ) : ℚ)), by {simp,})],
   rw nat.cast_lt,
   exact (nat.prime.pos hp.2),
  },
end

/-
Upper-bounds the product of geometric sums by
the product of primes. 
-/
lemma prod_sum_bound {n : ℕ}:
  ∏ p in ((range (n+1)).filter (λ p, nat.prime p)), (∑ k in Ico 0 (n+1), ((1/p)^k : ℚ))
  ≤ ∏ p in ((range (n+1)).filter (λ p, nat.prime p)), (p/(p-1) : ℚ) :=
begin 
  rw rw_the_prod,
    apply prod_le_prod,
    {intros i idef,
     apply sum_nonneg,
     intros j jdef,
     apply pow_nonneg,
     apply div_nonneg,
     exact zero_le_one,
     apply nat.cast_nonneg,
     },
    {intros p pdef,
     exact prod_sum_bound_pre pdef,
     },
end

/--
First step in linking the hamronic series to the
produc of geometric sums:
distributing the product of sums. 
-/
lemma the_great_split_part_1 {n : ℕ}:
  ∏ p in ((range (n+1)).filter (λ p, nat.prime p)), (∑ k in Ico 0 (n+1), ((1/p)^k : ℚ)) =
  ∑ valu in ((range (n+1)).filter (λ p, nat.prime p)).pi (λ p, (Ico 0 (n+1))), ∏ p in ((range (n+1)).filter (λ p, nat.prime p)).attach, ((1/(p.val))^(valu p.val p.prop) : ℚ)
  :=
by {apply prod_sum,}

/--
Second step in linking the hamronic series to the
produc of geometric sums:
lower-bounding the distributing the product of sums
by the sum on the subset obtained by filtering out
the terms who's value isn a 1/k for k∈[n]. 
-/
lemma the_great_split_part_2 {n : ℕ}:
  ∑ valu in (filter 
                ((λ  valu : Π (a : ℕ), a ∈ filter (λ (p : ℕ), nat.prime p) (range (n + 1)) → ℕ,
                              (∏ p in ((range (n+1)).filter (λ p, nat.prime p)).attach, (p.val)^(valu p.val p.prop)) ∈ (Icc 1 n)))
                (((range (n+1)).filter (λ p, nat.prime p)).pi (λ hmm, (Ico 0 (n+1))))),
                (1 / (∏ p in ((range (n+1)).filter (λ p, nat.prime p)).attach, ((p.val))^(valu p.val p.prop)) : ℚ)
  ≤ ∑ valu in ((range (n+1)).filter (λ p, nat.prime p)).pi (λ hmm, (Ico 0 (n+1))), (1 / (∏ p in ((range (n+1)).filter (λ p, nat.prime p)).attach, ((p.val))^(valu p.val p.prop)) : ℚ)
  :=
begin
  apply sum_le_sum_of_subset_of_nonneg,
  {apply filter_subset,},
  {intros i it ins,
   rw one_div,
   rw inv_nonneg,
   apply prod_nonneg,
   intros j jdef,
   apply pow_nonneg,
   apply nat.cast_nonneg,
   }, 
end

/--
A lemma that should be in mathlib, in my opinion.
Used in `quick_prime_decompo`.
-/
lemma prod_one
  {α : Type} [decidable_eq α] (s : finset α ): ∏ i in s, 1 = 1 :=
  by {--library_search, --fails
      apply finset.induction_on s,
      rw prod_empty,
      intros a s ans ih,
      rw prod_insert,
      rw ih,
      exact one_mul 1,
      exact ans,
      -- apply prod_eq_one,
      -- intros x xs,
      -- refl,
        -- alternative proof to the previous one
        -- In my defense: why is it not "prod_one" ?
      }


/-
For `the_great_split_part_3`, we need to show that all
numbers have a prime decomposition.
There are multiple notions of factorisation in mathlib,
which we now present
-/

-- This one I came accross only in the clean up phase of this file
#check nat.factorization
#eval nat.factorization 2023 7  --the valuation of prime factor 7 in 2023

-- Prime decomposition present as `factorization_prod_pow_eq_self`,
-- in terms of finsupp, not in the form:
-- example (n : ℕ):
--   n = ∏ f in n.factors.to_finset, f^(n.factorization f) :=
--     by {--library_search, --fails
--         }

-- This one I new about before formalizing `quick_prime_decompo`,
-- but it didn't appear useful, as it had no valuations ... 
#check nat.factors
#eval nat.factors 9
-- ... and prime decomposition was in the form of a product
-- over a list, where valuations made no appearance. 
#check nat.prod_factors
#check nat.factorization_prod_pow_eq_self

/--
Prime decomposition in the form of a function, in the sense that:
For each number `m` in 1,...,n, there is a valuation function `valu`
that has as inputs the primes in 1,...,n (as a pi-type), and returns
the power of that prime in the prime decomposition of `m`.
-/
lemma quick_prime_decompo {n : ℕ} (m: ℕ) (mdef: m ∈ Icc 1 n) :
  ∃ (valu : Π (valu : ℕ), valu ∈ filter (λ (p : ℕ), nat.prime p) (range (n + 1)) → ℕ),
  m = ∏ (x : {x // x ∈ filter (λ (p : ℕ), nat.prime p) (range (n + 1))}) in (filter (λ (p : ℕ), nat.prime p) (range (n + 1))).attach, ↑x ^ valu ↑x x.prop :=
begin
  revert mdef,
  -- We use strong induciton on `m`
  apply nat.strong_induction_on m,
  intros M ih Mdef,
  -- We disjoin cases on whether M is prime, in which case the
  -- valuation is the indicator of M, ...
  by_cases Mprime : nat.prime M,
  {set valuM := (λ (p : ℕ) (pdef : p ∈ filter (λ (p : ℕ), nat.prime p) (range (n + 1))) , if p = M then 1 else 0) with valuMdef,
   use valuM,
   rw valuMdef,
   simp_rw pow_ite,
   rw prod_ite,
   simp_rw pow_zero,
   rw finset.prod_const_one,
   rw mul_one,
   simp_rw pow_one,
   have simpli_the_set:
          filter (λ (x : {x // x ∈ filter (λ (p : ℕ), nat.prime p) (range (n + 1))}), ↑x = M) (filter (λ (p : ℕ), nat.prime p) (range (n + 1))).attach
          = {(⟨M , by {rw mem_filter, split, rw mem_range, rw mem_Icc at Mdef, linarith, exact Mprime,}⟩ : {x // x ∈ filter (λ (p : ℕ), nat.prime p) (range (n + 1))})} :=
      by {ext x,
          split,
          {intro xfil,
           simp only [true_and, finset.mem_attach, finset.mem_filter] at xfil,
           rw mem_singleton,
           apply subtype.eq,
           apply xfil,
           },
           {intro xsingle,
            simp only [true_and, finset.mem_attach, finset.mem_filter],
            rw mem_singleton at xsingle,
            --finish, -- works but slows down compilation
            rw xsingle,
            dsimp,
            refl,
            },
          },
   rw simpli_the_set,
   rw prod_singleton,
   dsimp, refl,
   },
  -- ... or M is not prime, in which case we factor it,
  -- and apply the induction hypothesis.
  -- We need to consider the case of M = 1 as well.
  apply lt_by_cases M 1,
  -- A technical and impossible case
  {intro c_lt_one,
   rw nat.lt_one_iff at c_lt_one,
   rw c_lt_one at Mdef,
   exfalso,
   rw mem_Icc at Mdef,
   norm_num at Mdef,
   },
   -- Case of M = 1: use the 0 valuation
  {intro c_eq_one,
    use (λ p pdef, 0),
    simp_rw pow_zero,
    rw prod_one (filter (λ (p : ℕ), nat.prime p) (range (n + 1))).attach,
    exact c_eq_one,
   },
   -- We may finally factor and use the induction assumption
   {intro two_le_M,
    obtain ⟨P,⟨P_def,facto⟩⟩ := nat.exists_prime_and_dvd (ne_of_gt two_le_M),
    -- In order to apply ih to P, we need the follwoing facts
    have PltM : P < M :=
      by {rw mem_Icc at Mdef,
          apply lt_of_le_of_ne,
          {apply nat.le_of_dvd _ facto,
           exact lt_of_lt_of_le zero_lt_one Mdef.1,
           },
          {intro con,
          rw con at P_def,
          exact Mprime P_def,},
          },
    have P_Icc : P ∈ Icc 1 n :=
      by {rw mem_Icc at *,
          split,
          {exact le_of_lt (nat.prime.one_lt P_def),},
          {apply le_trans _ Mdef.2,
           exact le_of_lt PltM,},
          },
    cases facto with d facto,
    -- Same thing with the other factor
    have dltM : d < M :=
      by {rw mem_Icc at Mdef,
          apply lt_of_le_of_ne,
          {have d_dvd := dvd_of_mul_left_eq P facto.symm,
           apply nat.le_of_dvd _ d_dvd,
           exact lt_of_lt_of_le zero_lt_one Mdef.1,
           },
          {intro con,
           rw con at facto,
           rw eq_comm at facto,
           rw nat.mul_left_eq_self_iff _ at facto,
           exact (nat.prime.ne_one P_def) facto,
           exact lt_trans zero_lt_one two_le_M,
           },
          },
    have d_Icc : d ∈ Icc 1 n :=
      by {rw mem_Icc at *,
          split,
          {by_contra' con,
           rw nat.lt_one_iff at con,
           rw con at facto,
           rw mul_zero at facto,
           rw facto at two_le_M,
           -- exact not_one_lt_zero, -- mathlib ?
           linarith,},
          {exact le_trans (le_of_lt dltM) Mdef.2,},
          },
    -- We apply the induction hypothesis
    obtain ⟨P_valu, P_valu_def⟩ : _ := ih P PltM P_Icc,
    obtain ⟨d_valu, d_valu_def⟩ : _ := ih d dltM d_Icc,
    -- The valuation of a product is the sum of valuations
    use (λ p pdef, P_valu p pdef + d_valu p pdef ),
    rw facto,
    rw [d_valu_def, P_valu_def],
    rw ← prod_mul_distrib,
    simp_rw ← pow_add,
    },
end



/--
A fibering lemma:
For a surjective map `i` as Pi-Types, so as to constrain it
to have domain `s`, with values in `t`,
- The preimages under `f` of the elements of `t` form a disjoint family
- `s` is a union of these perimages
-/
lemma surj_partition
  {α γ: Type} [decidable_eq α] [decidable_eq γ]
  {s : finset α} {t : finset γ} 
  (i : Π a ∈ s, γ)
  (imap : ∀ a ha, i a ha ∈ t)
  (i_surj : ∀ b ∈ t, ∃ a ha, b = i a ha) :
  ((t : set γ).pairwise_disjoint (λ x , (s.attach).filter (λ y, x = i y.val y.prop)))
  ∧ (s.attach = t.bUnion (λ x , (s.attach).filter (λ y : {z // z∈s}, x = i y.val y.prop))) :=
begin 
  split,
  {intros a ait b bit anb,
   dsimp,
   rw disjoint_iff_inter_eq_empty,
   ext x,
   simp only [true_and, finset.not_mem_empty, finset.mem_attach, not_and, finset.mem_filter, iff_false, finset.mem_inter],
   intros eqa eqb,
   apply anb,
   rw [eqa, eqb],
   },
  {ext x,
   split,
    {intro xs,
     rw mem_bUnion,
     use i x.val x.prop,
     split,
     exact imap x.val x.prop,
     rw mem_filter,
     split,
     exact xs,
     refl,},
    intro xuni,
    apply mem_attach s x,
    },
end

/-
It may very well be possible that the previous lemma is present in mathlib.
However, with libreary_serach failing, an nomenclature showing its limitations,
I proved it instead of looking further.
-/
#check bUnion_filter_eq_of_maps_to -- could you have guessed the name ?
-- #check pairwise_disjoint_of_maps_to --fails

/-
The following come close to what we want, and may possibly be used
as alternative in `sum_nonneg_surj`. However, the entire formalization
would have to be changed, as they don't work with Pi-types
-/
#check disj_Union_filter_eq_of_maps_to
#check sum_disj_Union


/--
For a nonnegative function `f` on `s`, and some `x∈s`, `f x ≤ ∑ y in s, f y`.
-/
lemma le_sum_mem_nonneg 
  {α β : Type} [decidable_eq α] [ordered_add_comm_monoid β] {s : finset α}
  (f : α → β) (hf : ∀ a, a∈s → 0 ≤ f a) (x : α) (hx : x∈s) :
  f x ≤ ∑ y in s, f y :=
begin
  rw ← (insert_erase hx),
  rw sum_insert,
  swap, 
  {apply not_mem_erase,},
  {nth_rewrite 0 ← add_zero (f x),
   apply add_le_add_left,
   apply sum_nonneg,
   intros i idef,
   exact hf i ((erase_subset x s) idef),
  },
end

/--
If we have a surjection `i` from `s` to `t` (as a Pi-type), and
functions `f` and `g` such that `f` is nonnegative and ` ∀ a ha, f a = g (i a ha)`,
then we may bound `(∑ x in t, g x) ≤ (∑ x in s, f x)`.
-/
lemma sum_nonneg_surj
  {α β γ: Type} [decidable_eq α] [decidable_eq γ] [ordered_add_comm_monoid β]
  {s : finset α} {t : finset γ} {f : α → β} {g : γ → β}
  (i : Π a ∈ s, γ) (hi : ∀ a ha, i a ha ∈ t) (h : ∀ a ha, f a = g (i a ha))
  (i_surj : ∀ b ∈ t, ∃ a ha, b = i a ha) (nonneg_fun: ∀ a, a∈s → 0 ≤ f a):
  (∑ x in t, g x) ≤ (∑ x in s, f x) :=
begin
  rw ← sum_attach, rw ← @sum_attach _ _ s _ f,
  obtain ⟨disj_fact, eq_fact⟩ : _ := surj_partition i hi i_surj,
  rw eq_fact,
  rw sum_bUnion disj_fact,
  rw ← @sum_attach _ _ t _ _,
  apply sum_le_sum,
  intros j jdef, simp,
  obtain ⟨k , ⟨kdef, keq⟩⟩ := i_surj j.val j.prop,
  rw ← subtype.val_eq_coe,
  rw keq,
  rw ← (h k kdef),
  have unsimp : f k = f (⟨k, kdef⟩ : {x // x∈s }) :=
    by {simp only [eq_self_iff_true, subtype.coe_mk],},
  rw unsimp, clear unsimp,
  apply le_sum_mem_nonneg (λ x : {x // x ∈ s}, f ↑x),
  swap,
  {rw mem_filter,
   split,
   apply mem_attach,
   simp only [eq_self_iff_true, subtype.coe_mk],
   },
  {intros a adef,
   simp only [],
   exact nonneg_fun ↑a a.prop,
  },
end


-- An alias ?
lemma nat.pos_iff_one_le {n : ℕ} : 0 < n ↔ 1 ≤ n :=
  by {exact nat.lt_iff_add_one_le}

-- A technical lemma used in `the_great_split_part_3`.
--For standard versions, consider the the #check that follow. 
lemma nat.le_prod_mem_pos
  {α : Type} [decidable_eq α] {s : finset α}
  (f : α → ℕ ) (hf : ∀ a, a∈s → 0 < f a) (x : α) (hx : x∈s) :
  f x ≤ ∏ y in s, f y  :=
begin
  rw ← (insert_erase hx),
  rw prod_insert,
  swap,
  apply not_mem_erase,
  nth_rewrite 0 ← mul_one (f x),
  apply nat.mul_le_mul_left,
  rw ← zero_add 1,
  rw ← nat.lt_iff_add_one_le,
  apply prod_pos,
  intros i idef, apply hf i _,
  exact (erase_subset x s) idef,
end

-- These have slightly different conditions and conclusions
-- Also, I didn't know the nomancalture for them
#check single_le_prod'
#check single_lt_prod'

-- An inequality used in `the_great_split_part_3`
lemma tec_ineq (n : ℕ) : n < 2^(n+1) :=
  by {induction n with n ih,
      norm_num,
      rw nat.succ_eq_add_one,
      rw [pow_add, pow_one, mul_two],
      apply nat.add_lt_add,
      exact ih,
      exact nat.one_lt_pow' n 0,
      }


/--
Final step in linking the hamronic series to the
produc of geometric sums:
upper-bound the harmonic sum with the filtered
sum of products. 
-/
lemma the_great_split_part_3 {n : ℕ}:
  ∑ k in Icc 1 n, (1/k : ℚ) 
  ≤ ∑ valu in (filter 
                ((λ  valu : Π (a : ℕ), a ∈ filter (λ (p : ℕ), nat.prime p) (range (n + 1)) → ℕ,
                              (∏ p in ((range (n+1)).filter (λ p, nat.prime p)).attach, (p.val)^(valu p.val p.prop)) ∈ (Icc 1 n)))
                (((range (n+1)).filter (λ p, nat.prime p)).pi (λ hmm, (Ico 0 (n+1))))),
                (1 / (∏ p in ((range (n+1)).filter (λ p, nat.prime p)).attach, ((p.val))^(valu p.val p.prop)) : ℚ) :=
begin
  -- i maps a valuation to the product of primes with these valuations
  set i := (λ (valu : Π (a : ℕ), a ∈ filter (λ (p : ℕ), nat.prime p) (range (n + 1)) → ℕ)
              (valu_def : valu ∈ (filter 
                                        ((λ  valu : Π (a : ℕ), a ∈ filter (λ (p : ℕ), nat.prime p) (range (n + 1)) → ℕ,
                                                      (∏ p in ((range (n+1)).filter (λ p, nat.prime p)).attach, (p.val)^(valu p.val p.prop)) ∈ (Icc 1 n)))
                                        (((range (n+1)).filter (λ p, nat.prime p)).pi (λ hmm, (Ico 0 (n+1)))))), 
                                        (∏ p in ((range (n+1)).filter (λ p, nat.prime p)).attach, ((p.val))^(valu p.val p.prop))) with idef,
  apply sum_nonneg_surj i,
  -- i maps one set of the sum to the other
   {intros valu valu_def,
    rw idef,
    simp only [finset.mem_Icc, finset.prod_congr, subtype.val_eq_coe],
    split,
    {apply one_le_prod'',
     intro p,
     apply nat.one_le_pow,
     apply nat.prime.pos,
     have := p.prop,
     rw mem_filter at this,
     exact this.2,
     },
    {rw mem_filter at valu_def,
     simp only [finset.mem_Icc, finset.mem_pi, finset.prod_congr, subtype.val_eq_coe] at valu_def,
     exact valu_def.2.2,
     },
  },
  -- equality of the images on the sets, when composing with i
  {intros valu valu_def,
   rw idef,
   simp only [nat.cast_prod, one_div, eq_self_iff_true, inv_inj, finset.prod_congr, nat.cast_pow, subtype.val_eq_coe],
  },
  swap 2,
  --nonnegativity of the functions we're comparing
  {intros valu valu_def,
  simp only [one_div, inv_nonneg, finset.prod_congr, subtype.val_eq_coe],
  apply prod_nonneg,
  intros j jdef,
  apply pow_nonneg,
  apply nat.cast_nonneg,
  },
  -- surjectivity : this is where we need `quick_prime_decompo`
  {intros m mdef,
   rw idef,
   simp?,
   obtain ⟨valu, valu_def⟩ : _ := quick_prime_decompo m mdef,
   use valu, split,
   {split,
     {-- We show that the valuation can't exceed n+1
      intros p pdef,
      by_contra' con,
      -- First, we show that a factor (with multiplicity) can't exceed the product
      have : (↑(⟨p , by {rw mem_filter, rw mem_range, exact pdef,} ⟩ : {x // x ∈ filter (λ (p : ℕ), nat.prime p) (range (n + 1))}))^(valu (↑(⟨p , by {rw mem_filter, rw mem_range, exact pdef,} ⟩ : {x // x ∈ filter (λ (p : ℕ), nat.prime p) (range (n + 1))})) (by {rw mem_filter, rw mem_range, exact pdef,})) ≤ m :=
      by { {rw valu_def,
          apply nat.le_prod_mem_pos (λ x : {x // x ∈ filter (λ (p : ℕ), nat.prime p) (range (n + 1))}, ↑x ^ valu ↑x x.prop  ),
          {intros q qdef, simp, apply pow_pos, apply nat.prime.pos,
           have : _ := q.prop, rw mem_filter at this, exact this.2,},
           apply mem_attach,},},
     simp only [subtype.coe_mk] at this,
     -- We lower bound the prime factor and make use of the
     -- contradictory assumption `con` to get the following:
     have problem : 2^(n+1) ≤ m :=
      by {calc
          2^(n+1) ≤ p^(n+1) :
            by {apply nat.pow_le_pow_of_le_left,
                apply nat.prime.two_le,
                exact pdef.2,}
          ... ≤ p^(valu p (by {rw mem_filter, rw mem_range, exact pdef,})) :
            by {apply nat.pow_le_pow_of_le_right,
                apply nat.prime.pos,
                exact pdef.2,
                exact con,}
          ... ≤ m :
            by {exact this,},
          },
     -- We use this bound and the assumption on `m` to
     -- contradict `2^(n+1)>n`
     rw mem_Icc at mdef,
     apply lt_irrefl n,
     apply lt_of_lt_of_le (tec_ineq n),
     apply le_trans problem mdef.2,
     },
    -- Some boudns that follow from `mdef` and `valu_def`
    {rw ←valu_def,
     rw mem_Icc at mdef,
     exact mdef,
     },
    },
  exact valu_def,
  },
end

/--
The center piece. 
We lower-bound the prime counting function by the harminic series!
-/
theorem the_great_merger {n : ℕ} :
  ∑ k in Icc 1 n, (1/k : ℚ)  ≤ (π n) + 1 :=
begin
  apply le_trans the_great_split_part_3,
  apply le_trans the_great_split_part_2,
  -- We have a rewrite of form 1/∏x = ∏1/x
  have rw_tec : ∀ (valu : Π (a : ℕ), a ∈ filter (λ (p : ℕ), nat.prime p) (range (n + 1)) → ℕ),
                (1 :ℚ) / ∏ (p : {x // x ∈ filter (λ (p : ℕ), nat.prime p) (range (n + 1))}) in (filter (λ (p : ℕ), nat.prime p) (range (n + 1))).attach, ((p.val ^ valu p.val p.prop) : ℚ ) =
                ∏ (p : {x // x ∈ filter (λ (p : ℕ), nat.prime p) (range (n + 1))}) in (filter (λ (p : ℕ), nat.prime p) (range (n + 1))).attach, (1/(p.val ^ valu p.val p.prop) : ℚ ) :=
    by {intro valu,
        nth_rewrite 0 ← ( @prod_eq_one _ _ _ (λ x, (1: ℚ) ) (filter (λ (p : ℕ), nat.prime p) (range (n + 1))).attach (by {intros x xdef, refl,})),
        apply prod_div_distrib.symm,
        },
  simp_rw rw_tec,
  -- We have a rewrite of form 1/(x^p) = (1/x)^p
  have rw_tec_2 : ∀ (valu : Π (a : ℕ), a ∈ filter (λ (p : ℕ), nat.prime p) (range (n + 1)) → ℕ),
                  ∏ (p : {x // x ∈ filter (λ (p : ℕ), nat.prime p) (range (n + 1))}) in (filter (λ (p : ℕ), nat.prime p) (range (n + 1))).attach, (1/(p.val ^ valu p.val p.prop) : ℚ ) =
                  ∏ (p : {x // x ∈ filter (λ (p : ℕ), nat.prime p) (range (n + 1))}) in (filter (λ (p : ℕ), nat.prime p) (range (n + 1))).attach, ((1/p.val) ^ valu p.val p.prop : ℚ ) :=
      by {simp_rw div_pow, simp_rw one_pow, intro valu, refl,},
  simp_rw rw_tec_2,
  clear rw_tec_2 rw_tec,
  -- We may now use:
  rw ← the_great_split_part_1,
  -- The great split is over, now we chain the bounds
  apply le_trans prod_sum_bound,
  rw order_the_prod,
  apply prod_ordered_primes_bound,
end

-- Another technical lemma that's mathlib material
lemma nat.Icc_split (a b c : ℕ) (h1: b ≤ c) (h2 : a ≤ b+1 ):
 (disjoint (Icc a b) (Icc (b+1) c))
 ∧ (Icc a c = (Icc a b) ∪(Icc (b+1) c))  :=
begin
  split,
  {rw disjoint,
   intros x xl xt,
   simp only [finset.bot_eq_empty, finset.le_eq_subset],
   intros y yx,
   -- rw @set.mem_empty_iff_false ℕ y, --hmm
   specialize xl yx,
   specialize xt yx,
   rw mem_Icc at *,
   linarith,
   },
   {ext x,
    split,
    {intro xb,
     rw mem_union,
     rw mem_Icc at *,
     by_cases q : x≤b,
     left,
     exact ⟨xb.1,q⟩,
     push_neg at q,
     rw nat.lt_iff_add_one_le at q,
     right,
     rw mem_Icc,
     exact ⟨q,xb.2⟩,
     },
     {intro xu,
      rw mem_union at xu,
      rw mem_Icc at *,
      cases xu,
      exact ⟨xu.1, le_trans xu.2 h1⟩,
      rw mem_Icc at *,
      exact ⟨le_trans h2 xu.1, xu.2⟩,
      },
    },
end


/--
Lower-bounding harminoc sums up to the `2^n`th term by `n/2`.
-/
lemma harmonic_lb :
  ∀ n : ℕ,  (n/2 : ℚ) ≤ ∑ k in Icc 1 ((2: ℕ)^n), (1/k : ℚ) :=
begin
  intro n,
  induction n with n ih,
  {simp only [one_div, algebra_map.coe_zero, zero_le_one, algebra_map.coe_one,
              nat.nat_zero_eq_zero, zero_div, finset.Icc_self, inv_one,
              finset.sum_singleton, pow_zero, finset.sum_congr],
  },
  {rw nat.succ_eq_add_one,
   -- We split the sum in half by splitiing the interval in half
   obtain ⟨split_disj, split_union⟩ := nat.Icc_split 1 (2^n) (2^(n+1))
      (by {apply pow_le_pow, norm_num, apply nat.le_succ,})
      (by {exact le_add_self,}),
   rw split_union,
   rw sum_union split_disj,
   push_cast,
   rw add_div,
   -- We may use the induciton hypothesis to handle the first half
   apply add_le_add ih,
   clear split_disj split_union,
   -- Next we work on lower-bounding the other half by the sum
   -- of its smallest term
   have rw_half : (1/2 : ℚ) = ((2^n)/(2^(n+1)) : ℚ) :=
    by {rw div_eq_div_iff,
        {rw one_mul,
         nth_rewrite_rhs 1 ← (@pow_one ℚ _ 2),
         rw ← pow_add,
         },
         {norm_num,},
         {apply ne_of_gt,
          apply pow_pos,
          norm_num,
          },
        },
   rw rw_half, clear rw_half,
   rw div_eq_mul_one_div,
   -- This will be the size of the constant sum:
   have Icc_size : (Icc ((2^n)+1) (2^(n+1))).card = 2^n :=
    by {rw nat.card_Icc,
        rw nat.sub_eq_iff_eq_add _,
        {rw ← add_assoc,
         rw ← mul_two,
         rw nat.succ_inj',
         rw [pow_add, pow_one],
         },
         {apply nat.succ_le_succ,
          apply pow_le_pow,
          norm_num,
          apply nat.le_succ,
          },
        },
   apply_fun (λ x, (x : ℚ)) at Icc_size,
   push_cast at Icc_size,
   rw (show (0 : ℚ)+1+1=2, by {norm_num,}) at Icc_size,
   rw ← Icc_size, clear Icc_size,
   -- Here, we introduce the constant sum:
   rw card_eq_sum_ones,
   push_cast,
   rw sum_mul,
   -- We may now proceed with bounding terms:
   rw (show (0 : ℚ)+1=1, by {norm_num,}),
   apply sum_le_sum,
   intros k kdef,
   rw one_mul,
   rw [one_div, one_div],
   rw inv_le_inv,
   {rw (show (2^(n+1) : ℚ) = ↑(2^(n+1)), by {simp,} ),
    rw nat.cast_le,
    rw mem_Icc at kdef,
    exact kdef.2,
    },
   {apply pow_pos,
    norm_num,},
   {rw nat.cast_pos,
    rw mem_Icc at kdef,
    apply lt_of_lt_of_le _ kdef.1,
    apply nat.succ_pos,
    },
   },
end

/-- The harmonic series in unbounded-/
lemma harmonic_unbounded :
  ¬ (∃ b : ℕ, ∀ n : ℕ, ∑ k in Icc 1 n, (1/k : ℚ) < b) :=
begin
  push_neg,
  intro b,
  use (2^(2*b)),
  apply le_of_eq_of_le _ (harmonic_lb (2*b)),
  simp only [algebra_map.coe_one, nat.cast_bit0, nat.cast_mul],
  -- rw mul_div_cancel''' --(ℚ, ×) is no a group
  rw mul_div_cancel_left,
  norm_num,
end


/--
### 4th proof of the infinitude of primes

We introduce the prime counting function `π`, which we
lower-bound by a certain product on prime numbers.

This product can be lower-bounded further until we reach
an expression that corresponds to a factored version of
the harmonic sums. 

Thus, we bounded the prime counting function by the
harmonic series, which is unbounded, so that there must
be infinitely many primes.
-/
theorem fourth_proof :
   {n : ℕ | n.prime }.infinite :=
begin
  rw set.infinite,
  intro con,
  -- We consider the number of primes
  set a := (con.to_finset).card with adef,
  -- Next, we get a larger harmonic sum
  have bound_pre := harmonic_unbounded,
  push_neg at bound_pre,
  obtain ⟨n, bound⟩ := bound_pre (a+2),
  clear bound_pre,
  -- then we use our bound
  replace bound := le_trans bound the_great_merger,
  rw [π] at bound,
  -- However, the card is of a set contained in the set of all primes
  have problem : (filter (λ (p : ℕ), nat.prime p) (range (n + 1))).card ≤ a :=
    by {rw adef,
        apply card_le_of_subset,
        intros x xdef,
        rw mem_filter at xdef,
        rw set.finite.mem_to_finset con,
        rw set.mem_set_of_eq,
        exact xdef.2,
        },
  simp only [algebra_map.coe_one, nat.cast_bit0, nat.cast_add] at bound,
  apply_fun (λ x : ℕ, (x : ℚ)) at problem,
  -- The bounds lead to a contradiciton
  linarith,
end


#check fourth_proof

