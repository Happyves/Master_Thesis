
/-
Copyright (c) 2023 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import tactic
import analysis.inner_product_space.basic
import analysis.inner_product_space.projection

/-!
# Lines in the plane and decompositions of graphs : Sylvester-Gallai

This file is part of a Master thesis project of formalizing some proofs from
"Proofs from THE BOOK" (5th ed.) by Martin Aigner and Günter M. Ziegler. 

We refer to chapter 11: "Pigeon-hole and double counting".
In this file, we formalize the Sylvester-Gallai theorem.


## Structure

- `Sylvester_Gallai` :
      Among any finite set of points not all on a line,
      we may find 2 of them such that no other point of
      the set is on the line they span.

- `Sylvester_Gallai_condition_fact` :
      It turns out that the condition that the points aren't
      aligned implies that there's at least 3 points. 

- `line` :
      We use a home-made definition of a line, and show a bunch
      of its properties, relating to membership, rewriting,
      nonemptyness, convexity, and completeness, the latter
      of which uses a `sorry`. Sorry. 

- `pigeons_on_a_line` :
      Is the argument for why one part of the line cut along
      the projection will conatin two of 3 points.
      It's used in the proof of `Sylvester_Gallai`, and it
      makes use of the pigeonhole principle.

- `point_line_finset` :
      The pairs of points and lines, so that the point isn't
      on the line, and the line is spanned by two points of
      the point set. 

- `point_line_proj` :
      Defines the projection of a point on a `line`.

- `min_dist` :
      Is the minimum distance among the point-line pairs
      of `point_line_finset`. 

-/


-- We'll work in a real Hilbert space (complete inner product space with dot-product in ℝ)
-- As you may check from the docstring of `inner_product_space`, we require `normed_add_comm_group`.
variables {E : Type} [_inst_1 : normed_add_comm_group E] [_inst_2 : inner_product_space ℝ E] [_inst_3 : complete_space E]


/--
The line passing through `a` and `b`, as a set.
Note: when `a=b` this is a point.
-/
def line (a b : E) : set E :=
  {x : E | ∃ t : ℝ, x = a + t•(b-a) }

/--
Lines are non-empty.
We need this to define projections in `point_line_proj`.
-/
lemma line_nonempty {a b : E} :
 (line a b).nonempty :=
begin
  use a,
  rw [line],
  simp only [set.mem_set_of_eq, exists_or_eq_left],
  use 0,
  simp only [add_zero, eq_self_iff_true, zero_smul],
end 

/-- A membership lemma -/
lemma left_mem_line {a b : E} :
  a ∈ line a b :=
begin
  rw line,
  use 0,
  rw zero_smul,
  rw add_zero,
end 

/-- A rewrite lemma -/
lemma line_comm {a b : E} :
  line a b = line b a :=
begin
  rw [line,line],
  ext x,
  split,
  {rintro ⟨tx ,xdef⟩,
   use (1-tx),
   rw sub_smul,
   rw one_smul,
   rw add_sub,
   rw add_sub_cancel'_right,
   rw (show a-b= -(b-a), by {rw neg_sub,}),
   rw smul_neg,
   rwa sub_neg_eq_add,
   },
  {rintro ⟨tx ,xdef⟩,
   use (1-tx),
   rw sub_smul,
   rw one_smul,
   rw add_sub,
   rw add_sub_cancel'_right,
   rw (show b-a= -(a-b), by {rw neg_sub,}),
   rw smul_neg,
   rwa sub_neg_eq_add,
   },
end 

/-- A membership lemma -/
lemma right_mem_line {a b : E} :
  b ∈ line a b :=
begin
  rw line_comm,
  apply left_mem_line,
end 

/--
Lines are complete. 
We need this to define projections in `point_line_proj`.
-/
lemma line_complete {a b : E} :
 is_complete (line a b) :=
begin
  apply is_closed.is_complete,
  apply is_seq_closed.is_closed,
  intros seq lim seq_mem lim_statement,
  simp [line] at seq_mem,
  replace seq_mem := classical.axiom_of_choice seq_mem,
  dsimp at seq_mem,
  cases seq_mem with seq_l seq_l_def,
  -- This is how far I'll go.
  sorry, 
end

/--
Lines are convex. 
We need this to define projections in `point_line_proj`.
-/
lemma line_convex {a b : E} :
 convex ℝ (line a b) :=
begin
  rw convex_iff_forall_pos,
  intros x xl y yl s t sp tp st,
  simp [line] at *,
  cases xl with tx tx_def,
  cases yl with ty ty_def,
  use (s*tx + t*ty),
  rw [tx_def,ty_def],
  rw [smul_add,smul_add],
  rw ← add_assoc,
  nth_rewrite_lhs 1 [add_comm],
  nth_rewrite_lhs 0 [← add_assoc],
  rw (show t•a+s•a = a,
      by {rw ← add_smul, rw add_comm at st, rw st, rw one_smul,}),
  rw add_assoc,
  rw add_left_cancel_iff,
  rw [smul_smul, smul_smul],
  rw ← add_smul, 
end 

/-- A rewrite lemma -/
lemma line_rw_of_mem
  {a b c : E} (h : c ∈ line a b) :
  line a b = line c (c+(b-a)) :=
begin
  rw [line,line],
  rw [line] at h,
  cases h with tc cdef,
  ext x,
  split,
  {rintro ⟨tx ,xdef⟩,
   use (tx - tc),
   rw cdef,
   rw add_sub_cancel',
   rw add_assoc,
   rw ← add_smul, 
   rw add_sub,
   rw add_sub_cancel',
   exact xdef,
  },
  {rintro ⟨tx ,xdef⟩,
   rw add_sub_cancel' at xdef,
   rw cdef at xdef,
   rw [add_assoc, ← add_smul] at xdef,
   use (tc+tx),
   exact xdef,
  },
end


/-- A rewrite lemma -/
lemma line_rw_of_mem_of_mem
  {a b c d: E}
  (hcd : c ≠ d)
  (hc : c ∈ line a b) (hd : d ∈ line a b):
  line a b = line c d :=
begin
  rw [line] at *,
  rw [line],
  cases hc with tc cdef,
  cases hd with td ddef,
  ext x,
  split,
  {rintro ⟨tx ,xdef⟩,
   have : td - tc ≠ 0 :=
    by {by_contra con,
        rw sub_eq_zero at con,
        apply hcd,
        rw [cdef, ddef, con],
        },
   use ((tx-tc)/(td-tc)),
   rw [cdef, ddef],
   simp only [add_sub_add_left_eq_sub],
   rw ← sub_smul,
   rw smul_smul,
   rw div_mul_cancel _ this,
   rw add_assoc,
   rw ←add_smul,
   rw add_sub,
   rw add_sub_cancel',
   exact xdef,
  },
  {rintro ⟨tx ,xdef⟩,
   rw [cdef, ddef] at xdef,
   simp only [add_sub_add_left_eq_sub] at xdef,
   rw ← sub_smul at xdef,
   rw smul_smul at xdef,
   rw add_assoc at xdef,
   rw ← add_smul at xdef,
   use (tc + tx * (td - tc)),
   exact xdef,
  },
end



/--
For 3 distinct points `a,b,c` on a line, and a 4th point `p`
on the line, we may find 2 distinct points `x,y` among `a,b,c`,
so that `p` and `y` are on the same side of the line wrt. `x`,
and in fact `y` is on the segment [x,p].
-/
lemma pigeons_on_a_line
  {a b c p : E }
  (hc : c ∈ line a b) (hp : p ∈ line a b)
  (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) :
  ∃ x, (x = a ∨ x = b ∨ x = c) ∧
  ∃ y, (y = a ∨ y = b ∨ y = c) ∧
  (y ≠ x) ∧
  ∃ t : ℝ, (0 < t ∧ t ≤ 1) ∧
  y = x + t•(p-x) :=
begin
  have ha := @left_mem_line _ _ _ _ a b,
  have hb := @right_mem_line _ _ _ _ a b,
  -- We "center" the line at `p`
  rw (line_rw_of_mem hp) at *,
  cases ha with ta adef,
  cases hb with tb bdef,
  cases hc with tc cdef,
  rw add_sub_cancel' at *,
  /-
  We cut the line into two sides delimited by `p`,
  The pigeonhole principle says that 2 of the three points
  `a,b,c` must be on a common side of `p`.
  -/
  -- The pigeonhole map
  let f := (λ t : ℝ, if ht : 0 ≤ t then 1 else 0),
  -- The size condition
  have cond_1 : ({0,1} : finset ℕ).card < ({ta,tb,tc} : finset ℝ).card :=
    by {have : ta ∉ ({tb,tc} : finset ℝ) :=
          by {intro con,
              rw finset.mem_insert at con,
              cases con,
              rw con at adef,
              apply hab,
              rw [adef],
              nth_rewrite 1 bdef,
              rw finset.mem_singleton at con,
              rw con at adef,
              apply hac,
              rw [adef, cdef],
              },
        nth_rewrite_rhs 0 finset.card_insert_of_not_mem this,
        clear this,
        have : tb ∉ ({tc} : finset ℝ) :=
          by {intro con,
              rw finset.mem_singleton at con,
              rw con at bdef,
              apply hcb,
              rw [bdef, cdef],
              },
        nth_rewrite_rhs 0 finset.card_insert_of_not_mem this,
        simp only [finset.card_doubleton, lt_add_iff_pos_right, eq_self_iff_true,
                   nat.lt_one_iff, finset.card_singleton],
        dec_trivial,
        },
  --The mapping condition
  have cond_2 : ∀ x, x ∈ ({ta,tb,tc} : finset ℝ)  → f x ∈ ({0,1} : finset ℕ) :=
    by {intros x xdef,
        rw finset.mem_insert,
        rw finset.mem_singleton,
        dsimp [f],
        by_cases q : 0 ≤ x,
        rw if_pos q,
        right,
        refl,
        rw if_neg q,
        left,
        refl,
        },
  -- We apply the pigeonhole principle
  obtain ⟨u,udef,v,vdef,unv,same⟩ := finset.exists_ne_map_eq_of_card_lt_of_maps_to cond_1 cond_2,
  clear cond_1 cond_2,
  dsimp [f] at same,
  -- We simplify "same"
  have signz : (0≤u ∧ 0≤v) ∨ (u<0 ∧ v<0)  :=
    by {cases (le_or_lt 0 u),
        rw if_pos h at same,
        rw eq_comm at same,
        rw ne.ite_eq_left_iff nat.one_ne_zero at same,
        left, exact ⟨h,same⟩,
        rw lt_iff_not_le at h,
        rw if_neg h at same,
        rw eq_comm at same,
        rw ne.ite_eq_right_iff nat.one_ne_zero at same,
        rw ← lt_iff_not_le at h,
        rw ← lt_iff_not_le at same,
        right, exact ⟨h,same⟩,
        },
  clear same,
  --wlog W : (0≤u ∧ 0≤v), --fails
  have tec : ∀ x, x ∈ ({ta,tb,tc} : finset ℝ) →
     (p + x•(b-a) = a ∨ p + x•(b-a) = b ∨ p + x•(b-a) = c) :=
      by {intros x xdef,
          rw finset.mem_insert at xdef,
          cases xdef,
          rw [xdef, ← adef],
          left, refl,
          rw finset.mem_insert at xdef,
          cases xdef,
          rw [xdef, ← bdef],
          right, left, refl,
          rw finset.mem_singleton at xdef,
          rw [xdef, ← cdef],
          right, right, refl,
          },
  cases signz,
  {--wlog H : v < u with Sym, --fails
   apply lt_by_cases v u,
   {intro vltu,
    use (p + u•(b-a)),
    split,
    {exact tec u udef,},
    use (p + v•(b-a)),
    split,
    {exact tec v vdef,},
     split,
     {intro con,
      rw add_right_inj at con,
      rw ←sub_eq_zero at con,
      rw ← sub_smul at con,
      rw smul_eq_zero at con,
      cases con,
      rw sub_eq_zero at con,
      rw con at vltu,
      exact (lt_irrefl u) vltu,
      rw sub_eq_zero at con,
      exact hab con.symm,
      },
     {use ((u-v)/u),
      have : u ≠ 0 :=
        by {intro con,
            apply lt_irrefl (0 : ℝ),
            rw con at vltu,
            exact lt_of_le_of_lt signz.2 vltu,
            },
      split,
      {split,
       rw div_pos_iff,
       left,
       split,
       rw sub_pos,
       exact vltu,
       apply lt_of_le_of_ne signz.1 (ne.symm this),
       rw div_le_iff (lt_of_le_of_ne signz.1 (ne.symm this)),
       rw one_mul,
       apply sub_le_self,
       exact signz.2,
       },
       {rw sub_add_cancel',
        rw ← neg_smul,
        rw smul_smul,
        rw add_assoc,
        rw ← add_smul,
        rw mul_neg,
        rw div_mul_cancel _ this,
        rw neg_sub,
        rw add_sub,
        rw add_sub_cancel',
        },
      },
   },
   {intro problem,
    exfalso,
    exact unv problem.symm,
    },
  -- same, with u and v swapped
  {intro vltu,
    use (p + v•(b-a)),
    split,
    {exact tec v vdef,},
    use (p + u•(b-a)),
    split,
    {exact tec u udef,},
     split,
     {intro con,
      rw add_right_inj at con,
      rw ←sub_eq_zero at con,
      rw ← sub_smul at con,
      rw smul_eq_zero at con,
      cases con,
      rw sub_eq_zero at con,
      rw con at vltu,
      exact (lt_irrefl v) vltu,
      rw sub_eq_zero at con,
      exact hab con.symm,
      },
     {use ((v-u)/v),
      have : v ≠ 0 :=
        by {intro con,
            apply lt_irrefl (0 : ℝ),
            rw con at vltu,
            exact lt_of_le_of_lt signz.1 vltu,
            },
      split,
      {split,
       rw div_pos_iff,
       left,
       split,
       rw sub_pos,
       exact vltu,
       apply lt_of_le_of_ne signz.2 (ne.symm this),
       rw div_le_iff (lt_of_le_of_ne signz.2 (ne.symm this)),
       rw one_mul,
       apply sub_le_self,
       exact signz.1,
       },
       {rw sub_add_cancel',
        rw ← neg_smul,
        rw smul_smul,
        rw add_assoc,
        rw ← add_smul,
        rw mul_neg,
        rw div_mul_cancel _ this,
        rw neg_sub,
        rw add_sub,
        rw add_sub_cancel',
        },
      },
   },
  },
  -- Negative u and v
  -- There are some minor changes in the proof
  {apply lt_by_cases v u,
   {intro vltu,
    use (p + v•(b-a)),
    split,
    {exact tec v vdef,},
    use (p + u•(b-a)),
    split,
    {exact tec u udef,},
     split,
     {intro con,
      rw add_right_inj at con,
      rw ←sub_eq_zero at con,
      rw ← sub_smul at con,
      rw smul_eq_zero at con,
      cases con,
      rw sub_eq_zero at con,
      rw con at vltu,
      exact (lt_irrefl v) vltu,
      rw sub_eq_zero at con,
      exact hab con.symm,
      },
     {use ((v-u)/v),
      have : v ≠ 0 := ne_of_lt signz.2,
      split,
      {split,
       rw div_pos_iff,
       right,
       split,
       rw sub_neg,
       exact vltu,
       exact signz.2,
       rw div_le_iff_of_neg (signz.2),
       rw one_mul,
       rw le_sub_self_iff,
       exact (le_of_lt signz.1),
       },
       {rw sub_add_cancel',
        rw ← neg_smul,
        rw smul_smul,
        rw add_assoc,
        rw ← add_smul,
        rw mul_neg,
        rw div_mul_cancel _ this,
        rw neg_sub,
        rw add_sub,
        rw add_sub_cancel',
        },
      },
   },
   {intro problem,
    exfalso,
    exact unv problem.symm,
    },
  -- same, with u and v swapped
  {intro vltu,
    use (p + u•(b-a)),
    split,
    {exact tec u udef,},
    use (p + v•(b-a)),
    split,
    {exact tec v vdef,},
     split,
     {intro con,
      rw add_right_inj at con,
      rw ←sub_eq_zero at con,
      rw ← sub_smul at con,
      rw smul_eq_zero at con,
      cases con,
      rw sub_eq_zero at con,
      rw con at vltu,
      exact (lt_irrefl u) vltu,
      rw sub_eq_zero at con,
      exact hab con.symm,
      },
     {use ((u-v)/u),
      have : u ≠ 0 := ne_of_lt signz.1,
      split,
      {split,
       rw div_pos_iff,
       right,
       split,
       rw sub_neg,
       exact vltu,
       exact signz.1,
       rw div_le_iff_of_neg (signz.1),
       rw one_mul,
       rw le_sub_self_iff,
       exact (le_of_lt signz.2),
       },
       {rw sub_add_cancel',
        rw ← neg_smul,
        rw smul_smul,
        rw add_assoc,
        rw ← add_smul,
        rw mul_neg,
        rw div_mul_cancel _ this,
        rw neg_sub,
        rw add_sub,
        rw add_sub_cancel',
        },
      },
   },
  },
end



open_locale classical
 -- due to decidability of a point belonging to a line or not

/--
For a finite set of points `P`, we consider the set of pairs
of points of `P` and lines through points of `P`, so that
the point isn't on the line.

This is modeled by represetning a line by its two points of `P`,
asking fro this triple of points to be distinct and finally asking
the first point to not be on the line spanned by the two others.
-/
noncomputable
def point_line_finset (P : finset E) :=
  (finset.univ : finset (↥P × (↥P × ↥P))).filter
    (λ t, (t.1 ≠ t.2.1) ∧
          (t.1 ≠ t.2.2) ∧
          (t.2.1 ≠ t.2.2) ∧
          (t.1.val ∉ line t.2.1.val t.2.2.val)
    )

/--
We obtain two distinct points from a set of size at least 2. 
Compare to `finset.card_eq_two` for sets of size 2. 
-/
lemma pair_of_2_le_card
  {α : Type} {s : finset α} (h : 2 ≤ s.card) :
  ∃ a b, (a∈s ∧ b∈s ∧  a≠b ) :=
begin
  have first : 0 < s.card := by {linarith,},
  rw finset.card_pos at first,
  obtain ⟨fst,fst_def⟩ :=  first,
  use fst,
  have second : 0 < (s.erase fst).card :=
    by {have := finset.card_erase_add_one fst_def,
        rw ← this at h,
        linarith,},
  rw finset.card_pos at second,
  obtain ⟨snd,snd_def⟩ :=  second,
  use snd,
  split, exact fst_def,
  split, apply (finset.erase_subset fst s) snd_def,
  intro con,
  rw ← con at snd_def,
  exact (finset.not_mem_erase fst s) snd_def,
end


-- I initially proved this, but it turns out that the pair was fine,
-- I'm keeping it here as it may be mathlib material.
lemma triple_of_3_le_card
  {α : Type} {s : finset α} (h : 3 ≤ s.card) :
  ∃ a b c, (a∈s ∧ b∈s ∧ c∈s  ∧ a≠b ∧ a≠c ∧ c≠b) :=
begin
  have first : 0 < s.card := by {linarith,},
  rw finset.card_pos at first,
  obtain ⟨fst,fst_def⟩ :=  first,
  use fst,
  have second : 0 < (s.erase fst).card :=
    by {have := finset.card_erase_add_one fst_def,
        rw ← this at h,
        linarith,},
  rw finset.card_pos at second,
  obtain ⟨snd,snd_def⟩ :=  second,
  use snd,
  have third : 0 < ((s.erase fst).erase snd).card :=
    by {have := finset.card_erase_add_one fst_def,
        have that := @finset.card_erase_add_one _ (s.erase fst) snd _ snd_def,
        rw ← this at h,
        linarith,},
  rw finset.card_pos at third,
  obtain ⟨thr,thr_def⟩ : _ :=  third,
  use thr,
  split, exact fst_def,
  split, apply (finset.erase_subset fst s) snd_def,
  split, apply (finset.subset.trans (finset.erase_subset snd (s.erase fst))  (finset.erase_subset fst s)) thr_def,
  split,
  intro con,
  rw ← con at snd_def,
  apply (finset.not_mem_erase fst s) snd_def,
  split,
  intro con,
  rw ← con at thr_def,
  rw finset.mem_erase at thr_def,
  apply (finset.not_mem_erase fst s) thr_def.2,
  intro con,
  rw ← con at thr_def,
  apply (finset.not_mem_erase thr (s.erase fst)) thr_def,
end

/--
I turns out that the condition that the points of `P`
aren't aligned implies that `P` has at least 3 points.
-/
lemma Sylvester_Gallai_condition_fact
  (P : finset E) (hSG : ¬ (∃ a b : E, ∀ p ∈ P, p ∈ line a b)) :
  3 ≤ P.card :=
begin
  by_contra' con,
  interval_cases P.card with hP,
  -- If there are no points, the ∀ statement of `hSG` is true. 
  {rw finset.card_eq_zero at hP,
   apply hSG,
   use 0, use 0,
   intros p problem,
   exfalso,
   rw hP at problem,
   exact (finset.not_mem_empty p) problem,
  },
  -- If there's one point, all points are on any line containing that point
  {rw finset.card_eq_one at hP,
   cases hP with e hP,
   apply hSG,
   use e, use e,
   intros p pdef,
   rw hP at pdef,
   rw finset.mem_singleton at pdef,
   rw pdef,
   apply left_mem_line,
   },
  -- If there are two points, all points are on the line they span
  {rw finset.card_eq_two at hP,
   rcases hP with ⟨a, b, anb, hP⟩,
   apply hSG,
   use a, use b,
   intros p pdef,
   rw hP at pdef,
   rw finset.mem_insert at pdef,
   cases pdef,
   rw pdef,
   apply left_mem_line,
   rw finset.mem_singleton at pdef,
   rw pdef,
   apply right_mem_line,
   },
end 


/--
Seeing as the "general position" implies that we have 3 points,
it also implies that the point-line-pairs set is non-empty.

We need this to define the minimum distance of points to lines
in `min_dist`. 
-/
lemma point_line_finset_nonempty
  (P : finset E) (hSG : ¬ (∃ a b : E, ∀ p ∈ P, p ∈ line a b)):
  (point_line_finset P).nonempty :=
begin
  have hP := Sylvester_Gallai_condition_fact P hSG,
  by_contra' con,
  simp only [finset.not_nonempty_iff_eq_empty, point_line_finset.equations._eqn_1] at con,
  obtain ⟨a,b,aP,bP,anb⟩ := pair_of_2_le_card (show 2 ≤ P.card, by {linarith,}),
  rw finset.filter_eq_empty_iff at con,
  simp? at con,
  specialize con,
  apply hSG,
  use a, use b,
  intros p pdef,
  specialize con p pdef a aP b bP,
  by_cases q1 : p = a,
  {rw q1, apply left_mem_line,},
  by_cases q2 : p = b,
  {rw q2, apply right_mem_line,},
  {rw ne.def at anb,
   exact con q1 q2 anb,
   },
end 


/--
For a triple of points, we define the projection of the first
on the line spanned by the two others.
-/
noncomputable
def point_line_proj
  (P : finset E) (hSG : ¬ (∃ a b : E, ∀ p ∈ P, p ∈ line a b))
  (t : (↥P × (↥P × ↥P))) :=
classical.some
  (@exists_norm_eq_infi_of_complete_convex _ _ _
    -- By projection, we mean distance minimiser
   (line t.2.1.val t.2.2.val)
   (by {apply line_nonempty,})
   (by {apply line_complete,})
   (by {apply line_convex,})
   t.1.val)
 

/--
The property of the projection `point_line_proj`:
it's on the line that the first point was projected on,
and it minimises the distance to that first point,
among points on the line.
-/
lemma point_line_dist_def
  (P : finset E) (hSG : ¬ (∃ a b : E, ∀ p ∈ P, p ∈ line a b))
  (t : (↥P × (↥P × ↥P))) :
  ∃ (H : (point_line_proj P hSG t) ∈ (line t.2.1.val t.2.2.val)),
  ‖t.1.val - (point_line_proj P hSG t)‖ =
  ⨅ (w : ↥(line t.2.1.val t.2.2.val)), ‖t.1.val  - ↑w‖ :=
begin
  rw point_line_proj,
  exact classical.some_spec (@exists_norm_eq_infi_of_complete_convex _ _ _
                                (line t.2.1.val t.2.2.val)
                                (by {apply line_nonempty,})
                                (by {apply line_complete,})
                                (by {apply line_convex,})
                                t.1.val),
end 


/--
We consider the minimum distance of a point to a line,
where the point and the line form a triple of the 
point-line-pair set `point_line_finset` we defined.
-/
noncomputable
def min_dist
  (P : finset E) (hSG : ¬ (∃ a b : E, ∀ p ∈ P, p ∈ line a b)) := 
  finset.min'
    (finset.image  
      (λ t : ↥P × ↥P × ↥P, ‖↑t.1 - (point_line_proj P hSG t)‖ )
                           -- `.val` raises an error.
      (point_line_finset P))
    (by {apply finset.nonempty.image,
         exact point_line_finset_nonempty P hSG,})


/--
A geometric lemma to handle a case of the 
the proof-by-picture of `Sylvester_Gallai`. 
-/
lemma SG_Thales_like 
 (x y z r t : E) (s : ℝ) (hs : 0 < s ∧ s < 1)
 (hy : y = x + s•(z-x)) (hr : r = x + s•(t-x))
 (htz : z ≠ t) :
 ‖y - r‖ < ‖z - t‖ :=
begin
  rw [hy, hr],
  simp only [add_sub_add_left_eq_sub],
  rw ← smul_sub,
  rw sub_sub_sub_cancel_right,
  rw norm_smul,
  rw real.norm_of_nonneg (le_of_lt hs.1),
  nth_rewrite 1 ← (one_mul ‖z - t‖),
  apply mul_lt_mul,
  exact hs.2,
  refl,
  rw norm_sub_pos_iff,
  exact htz,
  exact zero_le_one,
end



/--
A geometric lemma to handle a case of the 
the proof-by-picture of `Sylvester_Gallai`. 
-/
lemma SG_Pythagoras_workaround
 (x y z p t : E)
 (hyz : y = z)  (htz : t ≠ z)
 (izptp : inner (z - p) (t - p) ≤ (0 : ℝ))
 (iypxp : inner (y - p) (x - p) ≤ (0 : ℝ))
 (itzxz : inner (t - z) (x - z) ≤ (0 : ℝ))
 :
 ‖y - p‖ < ‖z - t‖ :=
begin
  have : ‖z-p‖ * ‖z-p‖ + ‖t-p‖ * ‖t-p‖ ≤  ‖z - t‖ * ‖z - t‖ :=
    by {rw ← (zero_add (‖z - t‖ * ‖z - t‖)),
        rw ← sub_le_iff_le_add,
        rw (show (z-t = (z-p)-(t-p)),
          by {simp only [eq_self_iff_true, sub_sub_sub_cancel_right, sub_left_inj]}),
        rw ← (zero_mul (2 : ℝ)),
        rw ← (div_le_iff _),
        rw ← real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
        exact izptp,
        norm_num,
        },
  by_contra con,
  push_neg at con,
  replace con := (show ‖z - t‖ * ‖z - t‖ ≤ ‖y - p‖ * ‖y - p‖,
    by {apply mul_le_mul,
        exact con,
        exact con,
        apply norm_nonneg,
        apply norm_nonneg,
        }),
  rw hyz at con,
  have eq : t = p :=
    by {rw ← sub_eq_zero,
        rw ← norm_eq_zero,
        rw ← sq_eq_zero_iff,
        rw pow_two,
        apply eq_of_le_of_not_lt,
        swap,
        {rw not_lt,
        apply mul_nonneg,
        apply norm_nonneg,
        apply norm_nonneg,
        },
        replace this := le_trans this con,
        nth_rewrite_rhs 0 ← (add_zero (‖z - p‖ * ‖z - p‖)) at this,
        apply @le_of_add_le_add_left _ _ _ _ (‖z - p‖ * ‖z - p‖) _ _ this,
        },
  rw hyz at iypxp,
  rw eq at itzxz,
  rw [← neg_sub] at itzxz,
  nth_rewrite 1 [ ← neg_sub] at itzxz,
  rw [inner_neg_left, inner_neg_right, neg_neg] at itzxz,
  have problem : z = p :=
    by {rw ← sub_eq_zero,
        rw ← norm_eq_zero,
        rw ← sq_eq_zero_iff,
        apply le_antisymm,
        swap,
        apply sq_nonneg,
        rw (show ‖z - p‖^2 = ↑(‖z - p‖^2 : ℝ), by {simp only [is_R_or_C.coe_real_eq_id, id.def, eq_self_iff_true, sq_eq_sq],}),
        push_cast,
        rw ← (@inner_self_eq_norm_sq_to_K ℝ _ _ _ _ (z-p)),
        nth_rewrite 1 (show z-p = (z-x)+(x-p), by {simp only [eq_self_iff_true, sub_add_sub_cancel, sub_left_inj],}),
        rw inner_add_right,
        exact add_nonpos itzxz iypxp,
        },
  rw ← problem at eq,
  exact htz eq,
end



/--
### The Sylvester-Gallai theorem:

Among any finite set of points not all on a line,
we may find 2 of them such that no other point of
the set is on the line they span. 
-/
theorem Sylvester_Gallai
  (P : finset E) (hSG : ¬ (∃ a b : E, ∀ p ∈ P, p ∈ line a b)) :
  ∃ a b ∈ P, a ≠ b ∧ (∀ p ∈ P, p ≠ a → p ≠ b → p ∉ line a b) :=
begin
  /- 
  We consider the minimum distance of the first of a triple of points
  to the line spanned by the other two, where the points are distinct,
  and the first isn't on the line spanned by the other two
  -/
  set d := min_dist P hSG with d_def,
  rw min_dist at d_def,
  have d_prop := 
    finset.min'_mem
      (finset.image  
        (λ t : ↥P × ↥P × ↥P, ‖↑t.1 - (point_line_proj P hSG t)‖ )
        (point_line_finset P))
      (by {apply finset.nonempty.image,
          exact point_line_finset_nonempty P hSG,}),
  rw ← d_def at d_prop,
  rw finset.mem_image at d_prop,
  rcases d_prop with ⟨t, tdef, tdist⟩,
  -- The two points from this minimum achieving line satisfy the result
  use t.2.1.val,
  split, exact t.2.1.prop,
  use t.2.2.val,
  split, exact t.2.2.prop,
  -- We prove this by contradiction
  by_contra' con,
  rw [point_line_finset] at tdef,
  rw finset.mem_filter at tdef,
  specialize con _,
  {intro K,
   apply tdef.2.2.2.1,
   exact subtype.eq K,
   },
  -- Hence, we assume there's a third point `q` on the line
  rcases con with ⟨q,qP,qnt21,qnt22,qline⟩,
  obtain ⟨proj_mem, proj_prop⟩ := point_line_dist_def P hSG t,
  -- We locate the projection wrt. the three points on the line
  obtain ⟨x,xdef,y,ydef,ynx,s, s_prop,yxs⟩ :=
    pigeons_on_a_line qline proj_mem
    (by {intro con, apply tdef.2.2.2.1, exact subtype.eq con,})
    (ne.symm qnt21)
    (qnt22),
  /- 
  We consider the point-line-pair made of the point bewteen
  the projection and another point of the line, and the new line
  spanned by that other point, and the initially projected point.
  We'll use this triple contradict minimailty of `d`.
  -/
  set t' := ((⟨y, by {cases ydef, rw ydef, exact t.2.1.prop,
                      cases ydef, rw ydef, exact t.2.2.prop,
                      rw ydef, exact qP,}⟩ : ↥P),
             ((⟨x, by {cases xdef, rw xdef, exact t.2.1.prop,
                      cases xdef, rw xdef, exact t.2.2.prop,
                      rw xdef, exact qP,}⟩ : ↥P),
              t.1)) with t'_def,
  -- The properties of the projection from that new triple
  obtain ⟨proj_mem', proj_prop'⟩ := point_line_dist_def P hSG t',
  simp_rw t'_def at proj_prop',
  simp_rw t'_def at proj_mem',
  have yline : y ∉ line x t.fst.val :=
    by {have : x ∈ line t.2.1.val t.2.2.val :=
          by {cases xdef, rw xdef, apply left_mem_line,
              cases xdef, rw xdef, apply right_mem_line,
              rw xdef, exact qline,},
        have that : y ∈ line t.2.1.val t.2.2.val :=
          by {cases ydef, rw ydef, apply left_mem_line,
              cases ydef, rw ydef, apply right_mem_line,
              rw ydef, exact qline,},
        intro thot,
        have line_eq : line t.2.1.val t.2.2.val = line x t.1.val :=
          by {have := (line_rw_of_mem_of_mem (ne.symm ynx) this that),
              rw this, clear this,
              have := (line_rw_of_mem_of_mem (ne.symm ynx) (@left_mem_line _ _ _ _ x t.1.val) thot),
              rw this,
              },
        apply tdef.2.2.2.2,
        rw line_eq,
        apply right_mem_line,
        },
  -- We consider the parallel to the first projection segement,
  -- passing through `y`, with a more adequate definition: 
  set r := (x + s•(t.1.val - x)) with r_def,
  by_cases Qs : s = 1,
  -- The case where `y = p`, and we use `SG_Pythagoras_workaround`. 
  {rw [Qs, one_smul, add_sub_cancel'_right] at yxs,
   rw [Qs, one_smul, add_sub_cancel'_right] at r_def,
   have := SG_Pythagoras_workaround x y (point_line_proj P hSG t) (point_line_proj P hSG t') t.1.val
           (yxs)
           (by {rw ←yxs,
                cases ydef, rw ydef, intro con, apply tdef.2.1, exact subtype.eq con,
                cases ydef, rw ydef, intro con, apply tdef.2.2.1, exact subtype.eq con,
                rw yxs,
                intro con,
                apply tdef.2.2.2.2,
                rw con,
                exact proj_mem,
                })
            (by {have := (@norm_eq_infi_iff_real_inner_le_zero _ _ _ _ (line_convex)) (point_line_proj P hSG t) _ proj_mem',
                 rw ←yxs at this, rw ←yxs,
                 apply this.mp proj_prop',
                 apply right_mem_line,
                 })
            (by {have := (@norm_eq_infi_iff_real_inner_le_zero _ _ _ _ (line_convex)) y _ proj_mem',
                 rw t'_def,
                 apply this.mp proj_prop',
                 apply left_mem_line,
                 })
            (by {have := (@norm_eq_infi_iff_real_inner_le_zero _ _ _ _ (line_convex)) t.1.val _ proj_mem,
                 apply this.mp proj_prop,
                 cases xdef, rw xdef, apply left_mem_line,
                 cases xdef, rw xdef, apply right_mem_line,
                 rw xdef, exact qline,
                 }),
   -- We have therefor found a smaller distance
   nth_rewrite 1 norm_sub_rev at this,
   rw subtype.val_eq_coe at this,
   rw tdist at this,
   -- We'll derive the contradiction from minimality
   apply (not_le_of_lt this),
   rw d_def,
   apply finset.min'_le,
   -- From here on, we need to do some justifications for why
   -- the supposed smaller distance is part of the set of distances
   rw finset.mem_image,
   use t',
   split,
   {rw [t'_def, point_line_finset],
    simp only [true_and, finset.mem_univ, subtype.mk_eq_mk, finset.mem_filter, subtype.coe_mk],
    split,
    intro con, apply ynx, simp? at con, exact con,
    split,
    intro con,
    replace con : y = t.1.val := by {rw ←con,},
    rw con at ydef,
    cases ydef with cy cy, apply tdef.2.1, exact (subtype.eq cy), 
    cases cy with cy cy, apply tdef.2.2.1, exact (subtype.eq cy),
    rw ← cy at qline, exact tdef.2.2.2.2 qline,
    split,
    intro con,
    replace con : x = t.1.val := by {rw ←con,},
    rw con at xdef,
    cases xdef with cy cy, apply tdef.2.1, exact (subtype.eq cy), 
    cases cy with cy cy, apply tdef.2.2.1, exact (subtype.eq cy),
    rw ← cy at qline, exact tdef.2.2.2.2 qline,
    exact yline,
    },
    simp only [t'_def, eq_self_iff_true, subtype.coe_mk],
    },
    -- The case where `y ≠p`, where we use `SG_Thales_like` .
    {replace Qs := lt_of_le_of_ne s_prop.2 Qs,
     have := SG_Thales_like x y (point_line_proj P hSG t) r t.1.val
                            s ⟨s_prop.1, Qs⟩ yxs r_def
                            (by {intro con,
                                 apply tdef.2.2.2.2,
                                 rw ← con,
                                 exact proj_mem,
                                 }),
     -- We've again found a smaller distance
     nth_rewrite 1 norm_sub_rev at this,
     rw subtype.val_eq_coe at this,
     rw tdist at this,
     -- We must relate it to distance from the set
     have transition : ‖y - (point_line_proj P hSG t')‖ ≤ ‖y - r‖ :=
      by {rw t'_def,
          rw proj_prop',
          have r_mem : r ∈ line t'.2.1.val t'.2.2.val :=
            by {simp [t'_def],
                use s,
                rw ← subtype.val_eq_coe,
                },
          apply @cinfi_le _ _ _ (λ (w : ↥(line t'.snd.fst.val t'.snd.snd.val)), ‖y - ↑w‖)
                          _ (⟨r, r_mem⟩  : ↥(line t'.snd.fst.val t'.snd.snd.val)),
          -- Thanks Yael !
          use (0 : ℝ),
          rw mem_lower_bounds,
          intros norm normdef,
          rw set.mem_range at normdef,
          cases normdef with point pointdist,
          rw ←pointdist,
          apply norm_nonneg, 
          },
    -- Minimality requires:
     have problem : d ≤ ‖y - point_line_proj P hSG t'‖ :=
      by {rw d_def,
          apply finset.min'_le,
          rw finset.mem_image,
          use t',
          split,
          {simp only [true_and, point_line_finset.equations._eqn_1, finset.mem_univ,
                      subtype.mk_eq_mk, finset.mem_filter, subtype.coe_mk],
           split,
           intro con, apply ynx, simp? at con, exact con,
           split,
           intro con,
           replace con : y = t.1.val := by {rw ←con,},
           rw con at ydef,
           cases ydef with cy cy, apply tdef.2.1, exact (subtype.eq cy), 
           cases cy with cy cy, apply tdef.2.2.1, exact (subtype.eq cy),
           rw ← cy at qline, exact tdef.2.2.2.2 qline,
           split,
           intro con,
           replace con : x = t.1.val := by {rw ←con,},
           rw con at xdef,
           cases xdef with cy cy, apply tdef.2.1, exact (subtype.eq cy), 
           cases cy with cy cy, apply tdef.2.2.1, exact (subtype.eq cy),
           rw ← cy at qline, exact tdef.2.2.2.2 qline,
           exact yline,
           },
          {simp only [t'_def, eq_self_iff_true, subtype.coe_mk],},
          },
    -- We reach the desired contradction
     apply lt_irrefl d,
     exact lt_of_le_of_lt (le_trans problem transition) this,
     },
end   




