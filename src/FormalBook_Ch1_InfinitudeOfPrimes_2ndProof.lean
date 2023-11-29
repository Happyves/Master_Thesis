/-
Copyright (c) 2023 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import tactic
import data.nat.prime
import data.nat.parity


/-!
# Six proofs of the inﬁnity of primes : 2nd proof

This file is part of a Master thesis project of formalizing some proofs from
"Proofs from THE BOOK" (5th ed.) by Martin Aigner and Günter M. Ziegler. 

We refer to chapter 1: "Six proofs of the inﬁnity of primes".
In this file, we formalize the "Second proof",
which makes use of Fermat numbers.

This proof is based on the formalization of Moritz Firsching,
who's orginial work can be found on the repository at:
https://github.com/eric-wieser/formal_book

We've made some modifications and additions.

## Structure

- `second_proof`:
      The conclusion of our work. We show that we can form
      a (infinite) sequence of primes all pairwise different.
- `second_proof_standardised` : 
      Infinitude of primes in terms of `set.infinite`,
      proven with `second_proof`.
- `F` :
      denotes  the Fermat number sequence.
- `fermat_product` :
      the recurrence relation satisfied by the Fermat numbers.
- `fermat_coprimes` :
      We show that the Fermat numbers are pairwise coprime.
      This is the the key step in showing infinitude of primes,
      as these numbers must have prime divisors, which must be
      pairwise different due to dividing coprime numbers. 

-/

open finset nat
open_locale big_operators


/-- The Fermat numbers-/
def F : ℕ → ℕ := (λ n, 2^(2^n) + 1)

/-- An evaluation lemma-/
lemma F₀: 
  F 0 = 3 :=
begin
  rw F,
  norm_num,
  --simp only [pow_zero, pow_one],
    --alternative to the previous line
end

/-- A technical lemma used to show the bound 2 < F n -/
lemma fermat_stricly_monotone {n : ℕ} :
  F n < F n.succ :=
begin
  rw F,
  rw add_lt_add_iff_right,
  rw pow_succ,
  refine (pow_lt_pow_iff one_lt_two).mpr _,
  norm_num,
end

/-- A technical lemma used to handle subtraction of naturals,
    as well as the fact that F n ≠ 1 -/
lemma fermat_bound (n : ℕ) :
  2 < F n :=
begin
  induction n with n ih,
  { rw F₀,
    norm_num, },
  { exact lt_trans ih fermat_stricly_monotone, },
end

/-- Fermat numbers are odd-/
lemma fermat_odd {n : ℕ} :
  odd (F n) :=
begin
  rw F,
  rw nat.odd_iff_not_even,
  rw even_add_one,
  rw not_not,
  rw even_pow,
  split,
  { exact even_two, },
  { exact ne_of_gt (pow_pos zero_lt_two _), },
end

/-- The recurence relation satisfied by Fermat numbers-/
lemma fermat_product (n : ℕ) :
  ∏ k in range n, F k = F n - 2 :=
begin
  induction n with n ih,
  trivial,
  rw prod_range_succ,
  rw ih,
  -- We prove a form without subtraction of naturals
  have h : (F n)*(F n) + 2 = (F n.succ) + 2 * (F n) := by
  {rw F,
   dsimp,
   simp only [add_mul, mul_add],
   simp only [one_mul, mul_one],
   simp only [pow_succ, two_mul],
   simp only [pow_add],
   ring,
  },
  -- Then we let linarith finish, using the identity and
  -- the following inequalities to certify subtraction isn't truncated. 
  have h_natsub_1 := le_of_lt (fermat_bound n),
  have h_natsub_2 := le_of_lt (fermat_bound n.succ),
  linarith,
end

/--
Fermat numbers are coprime. 

This follows from the recurrence relations and divisibility,
as well as the parity of Fermat numbers.
-/
lemma fermat_coprimes  (k n : ℕ) (h : k < n):
  coprime (F n) (F k) :=
begin
  -- Some notation and facts to ease exposition
  let m := (F n).gcd (F k),
  have h_n : m ∣ F n := (F n).gcd_dvd_left (F k),
  have h_k : m ∣ F k := (F n).gcd_dvd_right (F k),
  -- This will contradict Fermat numbers parity
  have h_m : m ∣ 2 :=
    by {-- The gcd divides the product of Fermat numbers up n-1
        -- since it divides the kth term
        have h_m_prod : m ∣ (∏ k in range n, F k) :=
          by {apply dvd_trans h_k,
              apply dvd_prod_of_mem,
              rw mem_range, exact h,
              },
        -- This product is also found in:
        have h_prod : (∏ k in range n, F k) + 2 = F n := by
        {rw fermat_product,
         have h_bound := lt_trans one_lt_two (fermat_bound n),
         exact nat.sub_add_cancel h_bound,
         },
        -- Hence we can use divisibility of linear combinations
        -- to conclude with our claim. 
        refine (nat.dvd_add_right h_m_prod).mp _,
        rw h_prod,
        exact h_n,
        },
  have h_one_or_two := (dvd_prime prime_two).mp h_m,
  cases h_one_or_two with h_one h_two,
  {exact h_one, },
  -- This is where the Fermat numbers parity, which we derived from
  -- their closed form, comes into play. 
  {exfalso,
   rw h_two at h_n,
   have h_even : even (F n) := even_iff_two_dvd.mpr h_n,
   have h_odd : odd (F n) := fermat_odd,
   exact (even_iff_not_odd.mp h_even) h_odd,
   },
end

/-- A technical lemma to allow for the use of `nat.exists_prime_and_dvd`
    on Fermat numbers -/
lemma fermat_neq (n : ℕ) :
   F n ≠ 1 :=
begin
  intro con,
  linarith [fermat_bound n],
end

/--
### 2nd proof of the infinitude of primes

Consider a sequence of prime divisors of the *Fermat numbers*,
one divisor per Fermat number.

These primes must be different: if the dividors were equal,
they would divide the coprime Fermat numbers, and yet, be prime,
which is impossible.
-/
theorem second_proof :
  ∃ (P : ℕ → ℕ), -- a function
  (∀ k, (P k).prime) ∧ -- with prime values
  (∀ k, ∀ q, k≠q → (P k) ≠ (P q)) -- the primes are different
  :=
begin
  -- We consider some list of prime dividors of the fermat numbers
  let prime_dvds := (λ n, @exists_prime_and_dvd (F n) (fermat_neq n)),
  obtain ⟨P, Pprop⟩ := classical.axiom_of_choice prime_dvds,
  dsimp at *, clear prime_dvds,
  -- These prime dividors must all be different
  use P,
  split,
  {intro k,
   exact (Pprop k).1,
  },
  {-- If the dividors were equal, they would divide coprime numbers,
   -- and yet, be prime, which is impossible. 
   intros k q knq problem,
   wlog C : k < q with Symmetry,
   {specialize Symmetry P Pprop q k,
    specialize Symmetry (ne.symm knq),
    specialize Symmetry (eq.symm problem),
    specialize Symmetry (lt_of_le_of_ne (not_lt.mp C) (ne.symm knq)),
    exact Symmetry,
    },
   have h_prime := (Pprop k).1,
   have h_dvd_1 := (Pprop k).2,
   have h_dvd_2 := (Pprop q).2,
   rw ← problem at h_dvd_2,
   have promblemo := eq_one_of_dvd_coprimes (fermat_coprimes k q C) h_dvd_2 h_dvd_1,
   exact (nat.prime.ne_one h_prime) promblemo,
    -- watch out for the simple `prime.ne_one`
    -- that won't recognize primes in naturals. 
  }
end

#check second_proof


/-- The standardised statement proven through Euclids proof-/
lemma second_proof_standardised :
  {n : ℕ | n.prime }.infinite :=
begin
  set f := classical.some second_proof with f_def,
  have f_prop := classical.some_spec second_proof, rw ← f_def at f_prop, 
  apply @set.infinite_of_injective_forall_mem ℕ ℕ _ {n : ℕ | n.prime } f,
  {rw function.injective,
   intros a b,
   contrapose,
   simp_rw ← ne.def, --simple rw is not enough
   exact f_prop.2 a b,
   },
  {simp_rw set.mem_set_of_eq,
   exact f_prop.1,
   },
end 




