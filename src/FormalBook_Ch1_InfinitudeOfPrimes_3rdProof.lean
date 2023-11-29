/-
Copyright (c) 2023 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import tactic
import data.nat.prime
import data.zmod.basic
import field_theory.finite.basic
import data.zmod.parity
-- simp experiment imports
  -- import algebra.algebra.subalgebra.basic
  -- import data.nat.cast.basic
  -- import algebra.group_power.lemmas
  -- import data.int.cast.basic


/-!
# Six proofs of the inﬁnity of primes : 3rd proof

This file is part of a Master thesis project of formalizing some proofs from
"Proofs from THE BOOK" (5th ed.) by Martin Aigner and Günter M. Ziegler. 

We refer to chapter 1: "Six proofs of the inﬁnity of primes".
In this file, we formalize the "Third proof",
which makes use of Mersenne numbers.


## Structure

- `third_proof`:
      We show that there are infinitely many primes, in the sense that
      for any finite set, there is a prime not contained in it.

- `third_proof_standardised` : 
      Infinitude of primes in terms of `set.infinite`,
      proven with `third_proof`.

-/

open nat finset


/--
### 3rd proof of the infinitude of primes

Assume that there are finitely many primes and
consider their largest one `p`. Next, consider a prime
divisor `q` of the *Mersenne number* `2^p - 1`.

- In ℤ/qℤ, the order of 2 divides p and is therefore p
- Also, the order of 2 divides q-1 by Fermat's little theorem

Hence, `p < q`, which contradicts maximality of p,
as q is also a prime.

-/
theorem third_proof :
  ∀ (s : finset ℕ), ∃ p, nat.prime p ∧ p ∉ s 
  :=
begin
  intro s,
  by_contra' h,
  set s_primes := s.filter nat.prime with s_primes_def,
  -- Let's add a membership definition lemma to ease exposition, as in the first proof
  have mem_s_primes : ∀ {n : ℕ}, n ∈ s_primes ↔ n.prime :=
    by {intro n,
        rw [s_primes_def, mem_filter, and_iff_right_iff_imp],
        exact h n,},
  -- A tecnical requirement to define the largest element of s_primes
  have s_primes_nonempty : s_primes.nonempty :=
    by {use 2,
        rw mem_s_primes,
        exact prime_two,},
  -- We consider the largest prime
  set p := (finset.max' s_primes s_primes_nonempty) with pdef,
  have p_prime : p.prime :=
    by {rw ← mem_s_primes,
        rw pdef,
        exact max'_mem s_primes s_primes_nonempty,},
  -- Next, we consider a prime divisor of the Mersenne number 2^p -1
  have dvd_Mers : ∃ q : ℕ, q.prime ∧ q ∣ (2^p -1) :=
    by {apply exists_prime_and_dvd,
        intro con, 
        rw nat.sub_eq_iff_eq_add -- requires nat, as `sub_eq_iff_eq_add` is for groups
          (one_le_two_pow p)
          at con,
        norm_num at con,
        nth_rewrite 1 ← pow_one 2 at con,
        replace con := (pow_right_injective (le_refl 2)) con,
        exact (nat.prime.ne_one p_prime) con,},
  rcases dvd_Mers with ⟨ q,q_prime, qd2p⟩, 
  -- Now, we switch to the finite field ℤ/qℤ  
  rw ← zmod.nat_coe_zmod_eq_zero_iff_dvd at qd2p,
  -- A technical lemma needed to show `odq`.
  have q_tec : q ≠ 2 :=
    by {intro con,
        rw con at qd2p, -- click on ↑ in the infoview to see the difference
        rw zmod.eq_zero_iff_even at qd2p,
        rw even_sub (one_le_two_pow p) at qd2p,
        simp only [nat.not_even_one, iff_false] at qd2p,
        rw even_pow at qd2p,
        exact qd2p ⟨even_two, (nat.prime.ne_zero p_prime)⟩, 
        },
  -- We may then use group theory to get:
  have odq : order_of (2 : zmod q) ∣ (q-1) :=
    by {haveI : fact (nat.prime q) := fact.mk q_prime, --this has been improved in lean 4
        -- This is the name and variant of Fermat's little theorem (as a consequence of Lagranges theorem):
        apply zmod.order_of_dvd_card_sub_one, -- required the instance
        apply ring.two_ne_zero,
        rw zmod.ring_char_zmod_n,
        exact q_tec},
  clear q_tec,
  simp? at qd2p,
    -- Note: check simp? in messages. Replacing simp with the message
    -- will fail, even if the library of the commands used is imported.  
  rw sub_eq_zero at qd2p,
  -- We use some more group theory to get:
  have odp : order_of (2 : zmod q) ∣ p := order_of_dvd_of_pow_eq_one qd2p,
  clear qd2p,
  -- Since the order of 2 divides a prime, we have:
  rw (dvd_prime p_prime) at odp,
  cases odp,
  -- Recall that q is a prime, and we showed it was different then 2,
  -- so that this case for `odp` is false, though we show it differently. 
  {rw order_of_eq_iff (show 0<1, by {exact zero_lt_one,}) at odp,
   have error_1 : (2 : zmod q) = 1 := by {rw ← pow_one (2 : zmod q), exact odp.1,},
   have error_2 : (2 : zmod q) ≠ 1 :=
      by {haveI : fact (nat.prime q) := fact.mk q_prime,
            -- allows us to recall that `zmod q` is a group
            -- so that we may use `sub_eq_zero`.
          intro h,
          rw ← sub_eq_zero at h, -- else, norm_num fails
          norm_num at h,},
  exact error_2 error_1,
  -- Note: direct applications of norm_num, possibly with rw ← sub_eq_zero and one_ne_zero are cumbersome too
  },
  rw odp at odq, 
  -- A consequence on the sizes:
  have dvd_bound_pre : p ≤ q-1 :=
    by {exact le_of_dvd
                (show 0<(q-1),
                  by {apply nat.sub_pos_of_lt,
                      exact prime.one_lt q_prime,})
                odq,
        },
  have dvd_bound : p < q :=
    by {linarith [show 1≤q, by {apply le_of_lt (prime.one_lt q_prime),}],
        -- Unfortunately, there is no `nat.prime.one_le`
        },
  clear dvd_bound_pre,
  rw pdef at dvd_bound,
  -- Yet, q is in the set `s_primes` and should be smaller then its maximum
  have problem : q ≤ s_primes.max' s_primes_nonempty := 
    by {apply le_max', rw mem_s_primes, exact q_prime,},
  -- We've reach our desired contradiction:
  exact (not_le_of_lt dvd_bound) problem,
  --linarith,
    -- alternative to the previous line
end


#check third_proof


/-- The standardised statement proven through Euclids proof-/
lemma third_proof_standardised :
  {n : ℕ | n.prime }.infinite :=
begin
  rw set.infinite,
  intro con,
  obtain ⟨p, ⟨p_prop, p_mem⟩⟩ := third_proof (set.finite.to_finset con),
  apply p_mem,
  rw set.finite.mem_to_finset con,
  rw set.mem_set_of_eq,
  exact p_prop,
end


