/-
Copyright (c) 2023 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import ring_theory.int.basic
import topology.basic
import tactic
import analysis.p_series --Deleting this import will yield unexpected errors

/-!
# Six proofs of the inﬁnity of primes : 5th proof

This file is part of a Master thesis project of formalizing some proofs from
"Proofs from THE BOOK" (5th ed.) by Martin Aigner and Günter M. Ziegler. 

We refer to chapter 1: "Six proofs of the inﬁnity of primes".
In this file, we formalize the "Fifth proof",
which makes use of Topology.


## Structure

- `fifth_proof` :
      We show that there are infinitely many primes,
      in the standardised sense for infinity.
- `bona_fide_topology` :
      Is the topology on ℤ we use throughout the proof. 
      It's based on the sets `N`.
- `two_units_not_open` :
      Is the proof that the pathological set {-1,1} isn't open.
- `univ_sdiff_units_as_prime_union` :
      Is the proof that {-1,1}ᶜ is a union of closed sets,
      indexed by the primes.


-/

/-- Two-way infinite arithmetic progressions-/
def N (a b : ℤ) : set ℤ := {x | ∃ n : ℤ, x = a + b*n}

/-- The curious topology on ℤ -/
instance bona_fide_topology : topological_space ℤ :=
{-- First, we define the property of a set being open in the topology
 is_open := (λ O, (O = ∅) ∨ (∀ a ∈ O , ∃ b : ℤ, ∃ b_tec : 0<b, (N a b) ⊆ O)),
 -- The universal set should be open 
 is_open_univ := by {--simp, use 1, exact zero_lt_one, -- the power of simp 
                     right,
                     intros a auniv,
                     use 1,
                     use zero_lt_one,
                     apply set.subset_univ,
                     },
 -- Intersections of open sets should be open                  
 is_open_inter := by {intros s t sO tO,
                      -- First, we discuss the empty cases
                      cases sO, left, rw sO, exact set.empty_inter t,
                      cases tO, left, rw tO,  exact set.inter_empty s,
                      -- Next come the non-empty cases
                      right,
                      intros a auniv,
                      specialize sO a, specialize tO a,
                      have ais : a∈s := set.mem_of_mem_inter_left auniv,
                      have ait : a∈t := set.mem_of_mem_inter_right auniv,
                      specialize sO ais, specialize tO ait, clear ais ait,
                      rcases sO with ⟨bs, ⟨ bs_tec, sIn⟩⟩, rcases tO with ⟨bt, ⟨ bt_tec, tIn⟩⟩,
                      -- The common terms of the progressions is the progression with lcm bs bt
                      -- as step, but that with step bs*bt (which is contained in the first),
                      -- does the job too. 
                      use bs*bt,
                      split,
                      exact mul_pos bs_tec bt_tec,
                      simp only [N, set.subset_inter_iff],
                      split,
                      intros x xdef,
                      cases xdef with xn xeq,
                      have : x ∈ N a bs :=
                        by {rw N, use (bt*xn), rw ← mul_assoc, exact xeq,},
                      exact sIn this,
                      intros x xdef, cases xdef with xn xeq,
                      have : x ∈ N a bt :=
                        by {rw N, use (bs*xn), rw ← mul_assoc, nth_rewrite 1 mul_comm, exact xeq,},
                      exact tIn this,
                      },
 -- Arbitrary unions of open sets should be open
 is_open_sUnion := by {intros fam fam_isO,
                       right,
                       intros a aunion,
                       rw set.mem_sUnion at aunion, rcases aunion with ⟨s, ⟨sfam, as⟩⟩, 
                       specialize fam_isO s sfam,
                       cases fam_isO,
                       exfalso, rw fam_isO at as, exact set.not_mem_empty a as,
                       specialize fam_isO a as,
                       rcases fam_isO with ⟨b, ⟨b_tec, incl⟩⟩,
                       use b, use b_tec,
                       refine set.subset.trans incl _, -- apply leads to a strange error
                       exact set.subset_sUnion_of_mem sfam,},
}

/--
Expressing the complement of a two-way arithmetic progression
as a finite union of two-way arithmetic progressions.

This allows us to show that N is closed, in the next lemma.
-/
lemma N_as_a_comlpement (a b : ℤ) (b_tec : 0<b) :
  (N a b)ᶜ = (⋃ i ∈ (finset.Ico 1 b),  (N (a+i) b) ) :=
begin 
  ext x,
  simp?, -- the suggested "simp only" is not enough to get the same result.
  split,
  {intro xcomp,
   -- If x isn't on the arithmetic progression, we can consider
   -- its "remainder" modulo the progression
   use ((x-a)%b),
   split, split,
   {by_contra' con,
    have problem : ((x-a)%b) = 0 := by {linarith [int.mod_nonneg (x-a) (ne_of_gt b_tec)],},
    clear con,
    rw ← int.dvd_iff_mod_eq_zero at problem,
    cases problem with d ddef,
    apply xcomp,
    simp only [N, set.mem_set_of_eq],
    use d,
    rw sub_eq_iff_eq_add at ddef,
    rwa add_comm at ddef, -- Note the use of rwa
   },
   {exact int.mod_lt_of_pos (x-a) b_tec,},
   {simp only [N, set.mem_set_of_eq],
    use ((x-a)/b),
    rw add_assoc, --else the next rewrite fails
    rw int.mod_add_div (x-a) b,
    abel,},
  },
  {rintros ⟨i,⟨i_bounds,ai⟩⟩,
   intro con,
   -- We'll derive a contradiction from basic computations and comparisions
   simp only [N, set.mem_set_of_eq] at *,
   cases ai with n ndef, cases con with m mdef,
   have target : i = b*(m-n) :=
    by {linear_combination - ndef + mdef,
        -- rw ndef at mdef,
        -- rw add_assoc at mdef, nth_rewrite_lhs 1 add_comm at mdef,
        -- rw add_left_cancel_iff at mdef,
        -- rw [add_comm, eq_comm] at mdef,
        -- rw ← sub_eq_iff_eq_add at mdef,
        -- rwa [mul_sub, eq_comm],
          -- alternative to the previous line
        },
   apply lt_by_cases (m-n) 0,
   {intro q,
    linarith [show i<0, by {rw target, apply linarith.mul_neg q b_tec,}],},
   {intro q, rw [q, mul_zero] at target, linarith,},
   {intro q,
    linarith [show b≤i,
      by {rw target,
          rw int.pos_iff_one_le at q,
          nth_rewrite 0 ← (mul_one b),
          apply mul_le_mul,
          apply le_refl, exact q, exact zero_le_one, exact le_of_lt b_tec,}],},
   },
end

/-- The N sets are closed in our topology -/
lemma N_closed (a b : ℤ) (b_tec : 0<b) :
  is_closed (N a b) :=
begin
  rw ←is_open_compl_iff,
  rw N_as_a_comlpement a b b_tec,
  apply is_open_bUnion,
  simp?,
  intros i wierd,
  simp only [is_open, topological_space.is_open],
    -- unfold the meaning of open in our topology
  right,
  intros x xdef,
  use b, use b_tec,
  intros y ydef,
  simp only [N, set.mem_set_of_eq] at *,
  cases xdef with nx xeq, cases ydef with ny yeq,
  rw xeq at yeq,
  use (nx +ny),
  rw mul_add, rw ← add_assoc,
  exact yeq,
end

/-- We show that the pathological set {-1,1} isn't open-/
lemma two_units_not_open :
  ¬ (bona_fide_topology.is_open {(-1 : ℤ),1}) :=
begin
  intro con,
  simp? [topological_space.is_open] at con,
  cases con,
  {have problem : (-1 : ℤ) ∈ ∅ := by { rw ← con, apply set.mem_insert,},
   rw [set.mem_empty_iff_false] at problem,
   exact problem,
   },
  {obtain ⟨b , ⟨b_tec, incl⟩⟩ := con.2, clear con,
   rw [N] at incl,
   have : 1 + b ∈ {x : ℤ | ∃ (n : ℤ), x = 1 + b * n} :=
     by {rw [set.mem_set_of_eq], use 1, rw (mul_one b),},
   specialize incl this,
   cases incl,
   linarith,
   simp only [add_right_eq_self, set.mem_singleton_iff] at incl,
   apply lt_irrefl (0 : ℤ), convert b_tec, exact incl.symm,
  },
end


/--
The pathological set {-1,1} complement is the union of
arithmetic progressions with primes as steps. 
-/
lemma univ_sdiff_units_as_prime_union :
  ({(-1 : ℤ),(1 : ℤ) })ᶜ  = (⋃ p ∈ ({ x : ℕ | x.prime}),  (N 0 p)) :=
-- Note : {(-1 : ℤ),1} worked in the previous lemma, and fails here
begin
  ext x, split,
  {intro xuniv,
   simp [N] at *,
   -- We can disjoin an easy case that will allow us to work with primes later on
   by_cases z : x = 0,
  {use 2, -- any prime works, though 2 has `nat.prime_two`
   split,
   exact nat.prime_two,
   use 0, rw mul_zero, exact z,
   },
   -- Now, the absolute value of x is ≥ 2, and hence we may use
   -- `int.exists_prime_and_dvd`, which requires the following condition: 
   have condition : x.nat_abs ≠ 1 :=
     by {intro con, rw int.nat_abs_eq_iff at con,
         rw or.comm at con,
         exact xuniv con,},
   obtain ⟨p,⟨p_prime,p_dvd_x⟩⟩ := int.exists_prime_and_dvd condition,
   cases p_dvd_x with d ddef,
   use p.nat_abs,
   split,
   {rw ← int.prime_iff_nat_abs_prime, exact p_prime,},
   {cases (int.nat_abs_eq p),
    {use d, rwa ← h,},
    {use -d,rw [h, neg_mul] at ddef, rwa [mul_neg],},
    },
  },
  {simp [N],
   intros p p_prime d eq,
   intro con,
   rw or.comm at con,
   have tec := (@int.nat_abs_eq_iff x 1).mpr,
   push_cast at tec, rw zero_add at tec,
   replace con := tec con, clear tec,
   apply_fun int.nat_abs at eq,
   rw [con, int.nat_abs_mul, int.nat_abs_of_nat] at eq,
   apply nat.prime.not_dvd_one p_prime,
   use d.nat_abs,
   exact eq,
   },
end



/--
### 5th proof of the infinitude of primes

We define a topology on ℤ based on two-way infinite arithmetic progressions.

- In this topology {-1,1} isn't open
- {-1,1}ᶜ is a union of closed sets, indexed by the primes

Hence, if there were finitely many primes, {-1,1}ᶜ would be closed,
contradicting the fact that {-1,1} isn't open.

-/
theorem fifth_proof :
  ({ x : ℕ | x.prime}).infinite :=
begin
  rw [set.infinite],
  intro con,
  have pair_as_union := univ_sdiff_units_as_prime_union,
  have union_closed :
    is_closed (⋃ p ∈ ({ x : ℕ | x.prime}),  (N 0 p)) :=
      by {apply is_closed_bUnion,
          exact con,
          intros p pdef,
          apply N_closed,
          rw set.mem_set_of_eq at pdef,
          rw nat.cast_pos,
          exact nat.prime.pos pdef,
          },
  rw ← pair_as_union at union_closed,
  rw ←is_open_compl_iff at union_closed,
  rw compl_compl at union_closed,
  exact two_units_not_open union_closed,
end

#check fifth_proof


