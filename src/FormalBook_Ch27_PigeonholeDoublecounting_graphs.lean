
/-
Copyright (c) 2023 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import linear_algebra.bilinear_form
import linear_algebra.projective_space.independence
import data.real.sqrt
import algebra.big_operators.ring
import combinatorics.double_counting
import data.sym.card
import combinatorics.simple_graph.acyclic 
import combinatorics.simple_graph.degree_sum
import tactic

/-!
# Pigeon-hole and double counting : Graphs

This file is part of a Master thesis project of formalizing some proofs from
"Proofs from THE BOOK" (5th ed.) by Martin Aigner and Günter M. Ziegler. 

We refer to chapter 27: "Pigeon-hole and double counting".
In this file, we formalize the section "Graphs".


## Structure

- `max_edges_of_c4_free_Istvan_Reiman` :
      If a 4-cycle-free graph, the number of edges is upper-bounded
      by the following expression in the number of vertices |V|:
      ⌊(|V|/ 4)(1 + real.sqrt (4*|V| - 3))⌋

- `c4_free` :
      Defines the property of being 4-cycle-free

- `c4_free_common_neightbours` :
      In a 4-cycle-free graph,
      two vertices have at most one common neighbour.

- `double_counting_rel` :
      Is the double counting relation we use to get the first
      inequality, `first_ineq`.

- `Cauchy_Schwartz_int` :
      A version of Cauchy-Schwartz for vectors in ℤ 

- `Cauchy_Schwartz_in_action` :
      We use Cauchy-Schwartz to derive a further ineqaulity

- `common_neighbors_c4_free` :
      The converse to `c4_free_common_neightbours`.
      If any two vertices have at most one common neighbour,
      then the graph is 4-cycle-free.


-/



open finset simple_graph


variables {V : Type} -- The type of vertices


#check simple_graph.is_acyclic --source of inspiration for `c4_free`


/-- The graph contains no 4-cycle -/
def c4_free (G : simple_graph V) : Prop :=
  ∀ (v : V) (c : G.walk v v), ¬((c.is_cycle) ∧ (c.length = 4))

-- Alternatives ?
#check subgraph
#check is_subgraph


variables [fintype V]  --[decidable_eq V]
/-
We tried following mathlib conventions: stay as general as possible. 
Indeed, we can define 4-cycle free infinite graphs.
The `open_locale classical` makes the need for `[decidable_eq V]`
-/

#check degree
/-
The degree can be formulated as `(G.neighbor_set v).to_finset.card`,
and we use it as source of inspiration to define the number of
common neighbours.
-/


instance tec_tec : fintype ↥(∅ : set V) := infer_instance

open_locale classical

/-
Otherwise, we get decidability issues for `u ∈ (G.common_neighbors v w)`,
even with `[decidable_eq V]`.
-/

noncomputable
instance tec
  (G : simple_graph V) (v w : V) :
  fintype ↥(G.common_neighbors v w) :=
begin
  by_cases q : (G.common_neighbors v w).nonempty,
  {dsimp [set.nonempty] at q,
   --cases q with x xprop, --fails
   --rcases q with ⟨x, xprop⟩,  --fails
   set x := classical.some q with xdef,
   have xprop := classical.some_spec q,
   rw ← xdef at xprop,
   /-
   We derive finiteness by building a surjection from the type
   of common neighbours to V, which requires some dummy element
   from `G.common_neighbors v w` we can send elements of V not in
   `G.common_neighbors v w` to. (hence the case disjunction)
   -/
   apply @fintype.of_surjective V (↥(G.common_neighbors v w)) _ _
     (λ u : V, if h : u ∈ (G.common_neighbors v w)
               then (⟨u, h⟩ : ↥(G.common_neighbors v w))
               else (⟨x, xprop⟩ : ↥(G.common_neighbors v w))),
   simp only [function.surjective.equations._eqn_1, set_coe.forall],
   intros y ydef,
   use y,
   rw dif_pos ydef,
  },
  {rw set.not_nonempty_iff_eq_empty at q,
   rw q,
   apply tec_tec,
  },
end


#check finset.card_eq_two

/--
A technical lemma extracting a pair of elements from
a finset of size ≥ 2. Comapre to mathlib's `finset.card_eq_two`.
Unfortunately, `finset.two_le_card` doesn't exist.
-/
lemma pair_of_two_le_card
  {α : Type} {s : finset α} (h : 2 ≤ s.card) :
  ∃ a, ∃ b, (a∈s ∧ b∈s ∧ a≠b) :=
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
  split,
  exact fst_def,
  split,
  apply (finset.erase_subset fst s) snd_def,
  intro con,
  rw ← con at snd_def,
  apply (finset.not_mem_erase fst s) snd_def,
end

/--
In a 4-cycle-free graph,
two vertices have at most one common neighbour.
-/
lemma c4_free_common_neighbours
  (G : simple_graph V) (h : c4_free G) :
  ∀ v w, v≠w → ((common_neighbors G v w).to_finset).card ≤ 1 :=
begin
  intros v w vnw,
  -- We proceed by contradiction
  by_contra' con,
  rw nat.lt_iff_add_one_le at con,
  norm_num at con,
  -- We get 2 common neighbours, and their properties
  obtain ⟨a,⟨b,⟨useless1,⟨useless2,anb⟩⟩⟩⟩ := pair_of_two_le_card con,
  clear useless1 useless2,
  have adef := a.prop, --for readability
  have bdef := b.prop,
  dsimp [common_neighbors] at *,
  have vna := adj.ne adef.1,
  have wna := adj.ne adef.2,
  have vnb := adj.ne bdef.1,
  have wnb := adj.ne bdef.2,
  dsimp [c4_free] at h,
  -- We build a 4-cycle and use it to derive the contradiciton
  let c4 := (walk.cons (bdef.1) (walk.cons (G.adj_symm bdef.2) (walk.cons (adef.2) (walk.cons (G.adj_symm adef.1) (@walk.nil V G v))))),
  apply h v c4,
  have for_later_too : c4.length = 4 :=
    by {dsimp [c4],
        norm_num,
        },
  split,
  swap,
  exact for_later_too,
  --We must show that our construction is a 4-cycle
  {rw walk.is_cycle_def,
   split,
    {rw walk.is_trail_def,
     dsimp [c4],
     dsimp [list.nodup],
     repeat {
        rw list.pairwise_cons,
        split,
        intros e edef,
        fin_cases edef ;
          {rw ne.def,
           rw not_iff_not.mpr sym2.eq_iff,
           push_neg,
           split,
           repeat {intro problem,
                   {{exfalso, {{exact vnb problem} <|> {exact vnb problem.symm} <|> {exact vnw problem} <|> {exact vnw problem.symm} <|> {exact vna problem} <|> {exact vna problem.symm} <|> {exact wna problem} <|> {exact wna problem.symm} <|> {exact wnb problem} <|> {exact wnb problem.symm} <|> {exact anb problem} <|> {exact anb problem.symm}},}
                   <|> {{exact vnb} <|> {exact vnb.symm} <|> {exact vnw} <|> {exact vnw.symm} <|> {exact vna } <|> {exact vna.symm} <|> {exact wna} <|> {exact wna.symm} <|> {exact wnb} <|> {exact wnb.symm} <|> 
                    {intro bna, rw subtype.coe_inj at bna, exact anb bna} <|> {intro bna, rw subtype.coe_inj at bna, exact anb bna.symm} <|> {intro bna, rw subtype.coe_inj at problem, exact anb problem} <|> {intro bna, rw subtype.coe_inj at problem, exact anb problem.symm}}},},
          },
        },
     apply list.pairwise.nil,},
   split,
   {intro con,
    apply_fun walk.length at con,
    rw walk.length_nil at con,
    rw for_later_too at con,
    norm_num at con,
    },
   dsimp [c4],
   dsimp [list.nodup],
   repeat {
      rw list.pairwise_cons,
      split,
      rw ← ne.def at vnw,
      intros e edef,
      fin_cases edef ;
      {{exact vnb} <|> {exact vnb.symm} <|> {exact vnw} <|> {exact vnw.symm} <|> {exact vna } <|> {exact vna.symm} <|> {exact wna} <|> {exact wna.symm} <|> {exact wnb} <|> {exact wnb.symm} <|> 
                              {intro bna, rw subtype.coe_inj at bna, exact anb bna} <|> {intro bna, rw subtype.coe_inj at bna, exact anb bna.symm}},
      },
   apply list.pairwise.nil,
   },
end


/--
We define our double-counting relation:
a vertex and a pair of vertices are in relation,
is bothe vertices of the pair are incident
to the vertex.
-/
def double_counting_rel
  (G : simple_graph V ) (u : V) (e : sym2 V) :=
   ∀ v ∈ e, G.adj u v 

/--
A technical lemma to get an easy criterion for when
two pairs, as finsets, are equal.
-/
lemma finset.pair_eq
  {α : Type} {a b c d : α }:
  (({a,b} : finset α ) = {c,d} ) ↔ ((a=c ∧ b=d ) ∨ (a=d ∧ b=c)) :=
begin
  split,
  intro eq,
  by_cases q : c = d,
  {rw [q, pair_eq_singleton] at eq,
   left,
   split,
   rw q,
   repeat {rw ← mem_singleton, rw ← eq, simp,},
   },
  by_cases Q : a = c,
  {left,
   split,
   exact Q,
   rw Q at eq,
   nth_rewrite_lhs 0 pair_comm at eq,
   nth_rewrite_rhs 0 pair_comm at eq,
   rw eq_comm at eq,
   rw insert_inj (show d ∉ {c},
      by {intro con,
          rw mem_singleton at con,
          exact q con.symm,}) at eq,
  exact eq.symm,
  },
  right,
  split,
  have : a ∈ ({c, d} : finset α ) :=
    by {rw ←eq, simp only [true_or, eq_self_iff_true, finset.mem_insert, finset.mem_singleton],},
  rw mem_insert at this,
  cases this,
  exfalso,
  exact Q this,
  rw mem_singleton at this,
  exact this,
  have : c ∈ ({a, b} : finset α ) :=
    by {rw eq, simp only [true_or, eq_self_iff_true, finset.mem_insert, finset.mem_singleton],},
  rw mem_insert at this,
  cases this,
  exfalso,
  exact Q this.symm,
  rw mem_singleton at this,
  exact this.symm,
  intro rest,
  cases rest,
  repeat {rw [rest.1, rest.2],},
  rw pair_comm,
end

/--
We show that the pairs, among those that have different elements,
that are in relation with a given vertex `u` are in number
"(deg u) choose 2"

This is the first proof, which makes use of finset pairs
in the form of `finset.card_powerset_len 2`.
-/
lemma double_count_above
  (G : simple_graph V ) (u : V) :
  ((finset.bipartite_above (double_counting_rel G) ({e : sym2 V | ¬ e.is_diag}.to_finset)) u ).card
  = (G.degree u).choose 2 :=
begin
  simp only [finset.bipartite_above, simple_graph.degree, set.to_finset_set_of],
  -- We will put the pair of the relation in bijection
  -- with pairs of neighbours of `u`
  rw ← finset.card_powerset_len 2 (G.neighbor_finset u),
  rw filter_filter,
  let bij := (λ (e : sym2 V)
                (edef : e ∈ filter (λ (a : sym2 V), ¬a.is_diag ∧ double_counting_rel G u a) univ),
                (({e.out.1 , (sym2.out_fst_mem e).other } : finset V))),
  apply card_congr bij,
  --The mapping condition
  {intros e edef,
   rw mem_filter at edef,
   simp [double_counting_rel] at edef,
   simp only [bij],
   rw mem_powerset_len,
   /-
   There used to be a switch to `other' ` here ...
   the issue seems to be linked to the "only" in
   line `simp only [bij]`. Compare this to the
   "Injectivity" code block
   -/
   split,
   {intros x xdef,
    rw mem_neighbor_finset,
    rw mem_insert at xdef,
    cases xdef,
    rw xdef,
    exact edef.2 e.out.1 (sym2.out_fst_mem e),
    rw mem_singleton at xdef,
    rw xdef,
    convert edef.2 (sym2.out_fst_mem e).other (sym2.other_mem (sym2.out_fst_mem e)),
    },
    rw card_eq_two,
    use e.out.1,
    use (sym2.out_fst_mem e).other,
    split,
    {intro con, apply edef.1,
     rw ← (sym2.other_spec (sym2.out_fst_mem e)),
     rw sym2.mk_is_diag_iff,
     exact con,
    },
    refl,
    },
  -- Injectivity
  {intros e r edef rdef eq,
   simp [bij] at eq, -- using "only" will lead to failure
   rw ← (sym2.other_spec' (sym2.out_fst_mem e)),
   rw ← (sym2.other_spec' (sym2.out_fst_mem r)),
   rw sym2.eq_iff,
   rw ← finset.pair_eq, convert eq,
  },
  -- Surjectivity
  {intros p pdef,
   rw mem_powerset_len at pdef,
   obtain ⟨x,⟨y,⟨xny,xydef⟩⟩⟩ := card_eq_two.mp pdef.2,
   use ⟦(x,y)⟧,
   have : ⟦(x, y)⟧ ∈ filter (λ (a : sym2 V), ¬a.is_diag ∧ double_counting_rel G u a) univ :=
     by {rw mem_filter,
         simp only [true_and, finset.mem_univ, sym2.is_diag_iff_proj_eq],
         split,
         rw ne.def at xny,
         exact xny,
         simp [double_counting_rel],
         split,
         repeat {rw ← mem_neighbor_finset,
                 apply pdef.1,
                 rw xydef,
                 simp,},
         },
   use this,
   simp [bij],
   have that :=  (sym2.other_spec' (sym2.out_fst_mem ⟦(x, y)⟧)), rw sym2.eq_iff at that,
   cases that,
   {rw xydef,
    congr,
    exact that.1,
    exact that.2,
   },
   {rw xydef,
    rw pair_comm,
    congr,
    exact that.2,
    exact that.1,
    },
   },
end

--#eval (sym2.out_fst_mem ⟦(1, 2)⟧).other'
  -- then what does "This is the computable version of `mem.other`" in the docstring mean ?


/--
We show that the pairs, among those that have different elements,
that are in relation with a given vertex `u` are in number
"(deg u) choose 2"

This is the second proof, which makes use of smy2 pairs
in the form of `sym2.card_image_off_diag`.
-/
lemma double_count_above'
  (G : simple_graph V ) (u : V) :
  ((finset.bipartite_above (double_counting_rel G) ({e : sym2 V | ¬ e.is_diag}.to_finset)) u ).card
  = (G.degree u).choose 2 :=
begin
  simp [finset.bipartite_above, degree],
  rw ← sym2.card_image_off_diag,
  congr,
  ext x,
  simp [double_counting_rel],
  apply sym2.induction_on x,
  intros A B,
  split,
  {intro one,
   use A,
   use B,
   split,
   split,
   apply one.2 A _,
   exact sym2.mem_mk_left A B,
   split,
   apply one.2 B _,
   exact sym2.mem_mk_right A B,
   intro con,
   apply one.1,
   rw sym2.mk_is_diag_iff,
   exact con,
   refl,},
   {intro two,
   --rcases two with ⟨a, ⟨b ,⟨ua ,⟨ub, anb⟩ ⟩, ⟨eq⟩ ⟩⟩, 
    cases two with a h,
    cases h with b h,
    cases h with h eq,
    split,
    intro con,
    apply h.2.2,
    rw ←eq at con,
    rw sym2.mk_is_diag_iff at con,
    exact con,
    intros y ydef,
    rw ← eq at ydef,
    rw sym2.mem_iff at ydef,
    cases ydef,
    rw ydef,
    exact h.1,
    rw ydef,
    exact h.2.1,
    },
end


/--
We show that for distinct vertices `v` and `w`,
the number of vertices in relation with
the pair they make up, is at most 1.
-/
lemma double_count_below
  (G : simple_graph V ) (hG : c4_free G) (v w : V) (vnw : v ≠ w ):
  ((finset.bipartite_below (double_counting_rel G) (univ)) (⟦(v,w)⟧) ).card ≤ 1 :=
begin
  have := c4_free_common_neighbours G hG v w vnw,
  simp [finset.bipartite_below, double_counting_rel],
  dsimp [common_neighbors, neighbor_set] at this,
  simp at this,
  rw ← filter_and at this,
  convert this,
  ext x,
  rw [adj_comm],
  nth_rewrite 1 [adj_comm],
end 


open_locale big_operators


/--
The sum of the number of vertices in relation with a given pair,
taken over all pairs of distinct vertices, is less then
"|V| choose 2"
-/
lemma double_count_below_bound
  (G : simple_graph V ) (hG : c4_free G):
  ∑ e in ({e : sym2 V | ¬ e.is_diag}.to_finset), ((finset.bipartite_below (double_counting_rel G) (univ)) e ).card
  ≤ (fintype.card V).choose 2 :=
begin
  rw ← sym2.card_subtype_not_diag,
  rw ← finset.card_univ,
  rw card_eq_sum_ones,
  rw ← @sum_subtype _ _ _ (λ e : sym2 V, ¬e.is_diag) _ ({e : sym2 V | ¬ e.is_diag}.to_finset) _ (λ e : sym2 V, 1),
  swap,
  {intro e,
  simp,},
  apply sum_le_sum,
  intros e,
  apply sym2.induction_on e,
  intros x y xydef,
  dsimp,
  apply double_count_below G hG,
  simp at xydef,
  apply xydef,
end 


/--
We make use of double counting and the previous bounds
to get a relation linking degrees and the graph's order
-/
lemma first_ineq
  (G : simple_graph V ) (hG : c4_free G):
  ∑ u in (univ : finset V), (G.degree u).choose 2 
  ≤ (fintype.card V).choose 2 :=
begin
  simp_rw [← double_count_above' ],
  rw @sum_card_bipartite_above_eq_sum_card_bipartite_below _ _ (double_counting_rel G) (univ : finset V) ({e : sym2 V | ¬ e.is_diag}.to_finset) _,
  apply double_count_below_bound G hG,
end 

/--
Distributes sums of sumtractions.
Refer to `sum_sub_distrib` for instances of
`subtraction_comm_monoid`, which isn't the case for ℕ.
An equivalent in the sense of `sum_tsub_distrib`
doesn't exists in mathlib.
-/
lemma nat.sum_sub_distrib 
  {α : Type} (s : finset α) (f g : α → ℕ)
  (h : ∀ i, g i ≤ f i): -- i∈s would be better but then a different induction is necessary
  ∑ i in s, (f i - g i) = (∑ i in s, f i )- (∑ i in s, g i)  :=
begin 
  apply finset.induction_on s,
  simp,
  intros a s ans ih,
  rw [sum_insert,sum_insert, sum_insert],
  rw ih,
  repeat {swap, exact ans,},
  apply tsub_add_tsub_comm,
  exact h a,
  apply sum_le_sum,
  intros i is, exact h i,
end 


/-- A technical rewrite we separated from `first_ineq_rw` -/
lemma tec_stuff
  (n : ℕ) :
  2*((n*(n-1))/2) = n*(n-1) :=
begin 
  nth_rewrite 1 ← nat.mod_add_div (n*(n-1)) 2,
  rw self_eq_add_left,
  rw nat.mul_mod,
  have : (n % 2) * ((n - 1) % 2) = 0 :=
    by {rw mul_eq_zero,
        induction n with n ih,
        left,
        dec_trivial,
        cases ih,
        right,
        rw nat.succ_sub_one,
        exact ih,
        by_cases q : n = 0,
        rw q,
        dec_trivial,
        rw ← ne.def at q,
        rw ← nat.one_le_iff_ne_zero at q,
        left,
        have id : n.succ = (n - 1) + 2 :=
          by {rw nat.succ_eq_add_one, linarith,},
        rw id,
        rw nat.add_mod, 
        rw ih,
        dec_trivial,
        },
  rw this,
  dec_trivial,
end


lemma mathlib_is_a_desert
  (n m k: ℕ) :
  n≤m → (m - n ≤ k ↔ m ≤ k + n) :=
begin
  --library_search,
  intro h,
  nth_rewrite 1 ← nat.sub_add_cancel h,
  simp,
end

--#find _ → (_ - _ ≤ _ ↔ _ ≤ _ + _) -- timeout


/-- 
We rewrite the first inequality with
some algebraic manipulations and previous
equalities.
-/
lemma first_ineq_rw
  (G : simple_graph V ) (hG : c4_free G):
  ∑ u in (univ : finset V), (G.degree u)^2 
  ≤ (fintype.card V)*((fintype.card V) - 1) 
    + ∑ u in (univ : finset V), (G.degree u) :=
begin
  have := first_ineq G hG,
  rw [nat.choose_two_right] at this,
  simp_rw [nat.choose_two_right] at this,
  have that : monotone (λ x, 2*x) := 
    by {simp [monotone],},
  apply_fun (λ x, 2*x) at this using that,
  rw mul_sum at this,
  rw tec_stuff (fintype.card V) at this,
  simp_rw [tec_stuff] at this,
  rw nat.mul_sub_left_distrib at this,
  simp_rw [nat.mul_sub_left_distrib] at this,
  simp_rw [← pow_two, mul_one] at this,
  have tec : ∀ (i : V), G.degree i ≤ G.degree i ^ 2 :=
    by {intro i,
        by_cases q : (G.degree i) = 0,
        rw q,
        dec_trivial,
        nth_rewrite 0 [← mul_one (G.degree i)],
        rw pow_two,
        rw mul_le_mul_left,
        rw nat.one_le_iff_ne_zero,
        apply q,
        rw nat.lt_iff_add_one_le,
        rw zero_add,
        rw nat.one_le_iff_ne_zero,
        apply q,
        },
  rw nat.sum_sub_distrib at this,
  swap,
  exact tec,
  rw mathlib_is_a_desert _ at this,
  rw nat.mul_sub_left_distrib,
  rw [←pow_two,mul_one],
  exact this,  
  apply sum_le_sum,
  intros i idef,
  exact tec i,
end


/--
The Cauchy-Schwartz inequality, for integer vectors.
The only version of Cauchy-Schwartz in mathlib
that I'm aware of is `norm_inner_le_norm`,
which requires real or comlpexed valued vectors,
via instance `[_inst_1 : is_R_or_C 𝕜] `.
Therefore, we give a self contained proof.
-/
lemma Cauchy_Schwartz_int
  (v w : V → ℤ) (s : finset V):
  (∑ i in s, (v i)*(w i))^2 ≤ (∑ i in s, (v i)^2)*(∑ i in s, (w i)^2) :=
begin
  -- We start with this positive sum of squares
  have start :  0 ≤ (∑ i in s, (∑ j in s, ((v i)*(w j) - (v j)*(w i))^2 )) :=
    by {apply sum_nonneg,
        intros i idef,
        apply sum_nonneg,
        intros j jdef,
        apply sq_nonneg,
        },
  simp_rw sub_sq at start,
  -- We distribute the inner sum
  have rw_1 : ∀ i, (∑ j in s, (((v i)*(w j))^2 - 2*((v i)*(w j))*((v j)*(w i)) + ((v j)*(w i))^2 )) =
                   ((v i)^2)*(∑ j in s,(w j)^2) - 2*((v i)*(w i))*(∑ j in s,((v j)*(w j))) + ((w i)^2)*(∑ j in s,(v j)^2) :=
    by {intro i,
        rw sum_add_distrib,
        rw sum_sub_distrib,
        simp_rw mul_pow,
        rw ←mul_sum,
        rw ←sum_mul,
        nth_rewrite 1 mul_comm,
        have micro : ∀ j, 2*((v i)*(w j))*((v j)*(w i)) = (2*((v i)*(w i)))*((v j)*(w j)) :=
          by {intro j,
              ring,},
        simp_rw [micro],
        rw ←mul_sum,
        },
  simp_rw [rw_1] at start,
  clear rw_1,
  rw sum_add_distrib at start,
  rw sum_sub_distrib at start,
  rw [←sum_mul, ←sum_mul, ←sum_mul] at start,
  rw ←mul_sum at start,
  linarith,
end

/--
We use a technique consisting in applying Cauchy-Schwartz
with the all 1 vector to get a fruther inequality in our context. 
-/
lemma Cauchy_Schwartz_in_action
  (G : simple_graph V):
  ((∑ u in (univ : finset V), (G.degree u))^2 : ℤ)
  ≤ (fintype.card V) * (∑ u in (univ : finset V), (G.degree u)^2) :=
begin
  have := Cauchy_Schwartz_int (λ u, (G.degree u)) (λ u, (1 : ℤ)) (univ : finset V),
  simp_rw [mul_pow, one_pow, mul_one] at this,
  rw ← finset.card_univ,
  simp_rw [card_eq_sum_ones (univ : finset V)],
  rw mul_comm,
  --exact this, --coersion
  push_cast,
  rw zero_add,
  exact this,
end


lemma second_ineq
  (G : simple_graph V ) (hG : c4_free G) :
  ((∑ u in (univ : finset V), (G.degree u))^2 : ℤ)
  ≤ ((fintype.card V)^2)*((fintype.card V) - 1)
    + (fintype.card V)*(∑ u in (univ : finset V), (G.degree u)) :=
begin
  apply le_trans (Cauchy_Schwartz_in_action G),
  rw pow_two,
  rw mul_assoc,
  rw ←mul_add,
  by_cases q : 0 < (fintype.card V),
  rw mul_le_mul_left,
  swap 2,
  rw nat.cast_pos,
  exact q,
  have := first_ineq_rw G hG,
  rw ← @nat.cast_le ℤ _ _ _ _ at this,
  push_cast at this,
  exact this,
  have : (fintype.card V) = 0 := by {linarith,},
  rw this,
  simp,
end


lemma third_ineq
  (G : simple_graph V ) (hG : c4_free G) :
  (4*(G.edge_finset.card)^2 : ℝ)
  ≤ ((fintype.card V)^2)*((fintype.card V) - 1)
    + (fintype.card V)*2*(G.edge_finset.card) :=
begin
  rw (show (4 : ℝ)  = 2^2, by {norm_num1,}),
  rw ← mul_pow, 
  rw mul_assoc,
  have := sum_degrees_eq_twice_card_edges G,
    -- here is where "2|E| = ∑ deg" comes into play 
  apply_fun (λ x, (x : ℝ)) at this,
  push_cast at this,
  rw ← (show (2 : ℝ) = 0 + 1 + 1, by {norm_num}) at this,
  rw ← this,
  clear this,
  have :=  second_ineq G hG,
  have that :monotone (λ x : ℤ, (x : ℝ)) := by {simp [monotone],},
  apply_fun (λ x, (x : ℝ)) at this using that,
  simp at this,
  exact this,
end

/--
We isloate the algebraic manipulations needed to get
`max_edges_of_c4_free_Istvan_Reiman` from our previous
inequality, to ease noatation.
-/
lemma max_edges_of_c4_free_Istvan_Reiman_pre
  (a b : ℕ) 
  (ineq :   (4*(a)^2 : ℝ) ≤ ((b)^2)*((b) - 1) + (b)*2*(a)):
  ((a) : ℤ) ≤ ⌊((b) / 4 : ℝ)*(1 + real.sqrt (4*(b) - 3))⌋ :=
begin
  rw int.le_floor,
  simp only [int.cast_coe_nat],
  rw mul_add,
  rw mul_one,
  apply le_add_of_sub_left_le,
  -- We make use of the canoncic/normal form of 2nd degree equations 
  have canonic : (4 : ℝ)*((a - ((b) / 4))^2) ≤ ((((b)^2)/4)*(1+((4*(b)) -4))) :=
    by {rw [pow_two, sub_mul, mul_sub, mul_sub, ← pow_two],
        cancel_denoms,
        simp_rw mul_assoc,
        rw ← mul_add,
        rw mul_le_mul_left (show 0<(4: ℝ), by {norm_num}),
        cancel_denoms,
        ring_nf,
        rw (show (((4 * ↑((b))) - 4) : ℝ) = 4*(↑((b)) - 1),
              by {rw mul_sub, rw mul_one,}),
        rw add_mul,
        rw [show (16 : ℝ) = 4*4, by {norm_num} ],
        rw [show (8 : ℝ) = 4*2, by {norm_num} ],
        simp_rw [mul_assoc],
        rw ←mul_add,
        rw mul_le_mul_left (show 0<(4: ℝ), by {norm_num}),
        rw ← pow_two,
        rw ←mul_assoc,
        nth_rewrite 1 mul_comm,
        nth_rewrite 2 mul_comm, 
        rw ← mul_assoc,
        exact ineq,
        },
  rw ← (mul_le_mul_left (show 0<(2: ℝ), by {norm_num})),
  nth_rewrite 0 [show (4 : ℝ) = 2^2, by {norm_num} ] at canonic,
  rw ← mul_pow at canonic,
  replace canonic := real.le_sqrt_of_sq_le canonic,
  rw real.sqrt_mul at canonic,
  rw ← mul_assoc,
  have one : 2 * (↑((b)) / 4) = real.sqrt ((↑((b))^2) / 4) :=
    by {rw real.sqrt_div,
        rw real.sqrt_sq _,
        rw mul_div_left_comm,
        rw [show (2/4 : ℝ) = 1/2, by {norm_num} ],
        rw [show (4: ℝ) = 2*2, by {norm_num} ],
        rw real.sqrt_mul_self (show (0: ℝ) ≤ 2, by {norm_num}),
        ring,
        apply nat.cast_nonneg,
        apply sq_nonneg,
        },
  rw one,
  have two : (1 : ℝ) + (4 * ↑((b)) - 4) = 4 * ↑((b)) - 3 :=
    by {linarith,},
  simp_rw ← two,
  exact canonic,
  apply div_nonneg,
  apply sq_nonneg,
  norm_num,
end

-- Deriving the canonic form with `ring`
example (a b : ℕ) :
   (4*(a)^2 : ℝ) - ((b)^2)*((b) - 1) - (b)*2*(a) =(4 : ℝ)*((a - ((b) / 4))^2) - ((((b)^2)/4)*(1+((4*(b)) -4))) :=
begin
  ring,
end 


/--
If a 4-cycle-free graph, the number of edges is upper-bounded
by the following expression in the number of vertices |V|:
⌊(|V|/ 4)(1 + real.sqrt (4*|V| - 3))⌋ 
-/
theorem max_edges_of_c4_free_Istvan_Reiman
  (G : simple_graph V ) (hG : c4_free G) :
  ((G.edge_finset.card) : ℤ) ≤ ⌊((fintype.card V) / 4 : ℝ)*(1 + real.sqrt (4*(fintype.card V) - 3))⌋ :=
begin
  apply max_edges_of_c4_free_Istvan_Reiman_pre G.edge_finset.card (fintype.card V),
  exact third_ineq G hG,
end


/--
The converse to `c4_free_common_neightbours`.
If any two vertices have at most one common neighbour,
then the graph is 4-cycle-free.
-/
lemma common_neighbors_c4_free (G : simple_graph V)
  (h : ∀ v w, v≠w → ((common_neighbors G v w).to_finset).card ≤ 1 ) :
  c4_free G :=
begin
  revert h,
  rw c4_free,
  contrapose!, -- we show this by contraposition
  intro C,
  rcases C with ⟨v, ⟨cyc, ⟨cyc_cycle, cyc_len⟩⟩⟩,
  -- We unfold the cycle 
  cases cyc with _ _ a _ av cyc,
  exfalso, exact walk.is_cycle.not_of_nil cyc_cycle,
  cases cyc with _ _ b _ ba cyc,
  exfalso, simp only [simple_graph.walk.length_nil, nat.one_ne_bit0, zero_add, simple_graph.walk.length_cons] at cyc_len, exact cyc_len,
  cases cyc with _ _ c _ bc cyc,
  exfalso, simp only [simple_graph.walk.length_nil, zero_add, simple_graph.walk.length_cons] at cyc_len, norm_num at cyc_len,
  cases cyc with _ _ d _ dc cyc,
  exfalso, simp only [simple_graph.walk.length_nil, zero_add, simple_graph.walk.length_cons] at cyc_len, norm_num at cyc_len,
  simp at cyc_len,
  --norm_num at cyc_len, --fails, hence:
  have : cyc.length = 0 := by {linarith,},
  replace this := walk.eq_of_length_eq_zero this,
  -- We will show that two vertices on oppsite sides of
  -- the cycles have at least two neighbours in common
  use v, use b,
  simp [walk.is_cycle_def] at cyc_cycle,
  push_neg at cyc_cycle,
  split,
  exact cyc_cycle.1.2.1.2,
  have that : {a, c} ⊆ (G.common_neighbors v b).to_finset :=
    by {intros x xdef,
        rw mem_insert at xdef,
        cases xdef,
        rw xdef,
        simp [common_neighbors],
        exact ⟨av, (G.adj_symm ba)⟩, 
        rw mem_singleton at xdef,
        rw xdef,
        simp [common_neighbors],
        rw this at dc,
        exact ⟨(G.adj_symm dc), bc⟩,
        },
  --apply_fun finset.card at that using finset.card_mono, --fails
  have thot : ({a, c} : finset V).card = 2 :=
    by {rw card_insert_of_not_mem,
        rw card_singleton,
        intro con,
        rw mem_singleton at con,
        exact cyc_cycle.1.1.2.1.2 con,
        },
  apply lt_of_lt_of_le (show 1 < 2, by {norm_num,}),
  rw ← thot,
  apply card_le_of_subset that,  
end



variables (p : ℕ) [fact p.prime]
/-
Note : instance [nat.prime p] is a thing, but raises error
because `zmod p` isn't recognized as a field
-/

/--
Two vertices (points of the pejective space), are connected
by an edge iff they're orthogonal to one another. 
-/
def edge_relation
  (v w : (projectivization (zmod p) (fin 3 → (zmod p)))) :=
  (v ≠ w) ∧ (matrix.dot_product v.rep w.rep = 0) 


/--
The extremal graph that will be used to show that the bound
from `max_edges_of_c4_free_Istvan_Reiman` is tight. 
-/
def extremal_graph :
  simple_graph (projectivization (zmod p) (fin 3 → (zmod p))) :=
{adj := edge_relation p ,
 symm := by {rw [symmetric],
             intros v w rel,
             dsimp only [edge_relation] at *,
             split,
             exact ne.symm rel.1,
             rw matrix.dot_product_comm,
             exact rel.2,},
 loopless := by {rw [irreflexive],
                 intros v,
                 dsimp [edge_relation],
                 push_neg,
                 intro con,
                 exfalso,
                 exact con (eq.refl v),},
}

/--
A rewrite lemma characterizing neighbours in terms of orthogonality
-/
lemma neighbor_extremal_graph
  (v w : (projectivization (zmod p) (fin 3 → (zmod p)))):
  v ∈ (extremal_graph p).neighbor_set w
  ↔ (v ≠ w) ∧ (matrix.dot_product v.rep w.rep = 0):=
begin
  rw mem_neighbor_set,
  dsimp only [extremal_graph, edge_relation],
  rw [matrix.dot_product_comm, ne_comm],
end 

instance reminder : fintype (zmod p) := infer_instance
-- turns out only this instance is needed for .to_finset not to fail in Zp3_fin


noncomputable
instance Zp3_fin :
  fintype (projectivization (zmod p) (fin 3 → (zmod p))) :=
  --infer_instance --fails
begin
  apply @quotient.fintype {v : (fin 3 → (zmod p)) // v ≠ 0 }
        (by {apply fintype.subtype {v : (fin 3 → (zmod p)) | v ≠ 0 }.to_finset,
              intro x,
              simp only [true_and, finset.mem_univ, set.to_finset_congr, iff_self,
                        set.to_finset_set_of, ne.def, finset.mem_filter],}) 
        (projectivization_setoid (zmod p) (fin 3 → (zmod p)))
        _,
end


/--
To make use of orthogonality related theorems,
we need to remind ourselves that the dot-product
is a bilinear form. 
-/
def dotp : bilin_form (zmod p) (fin 3 → (zmod p)) :=
{bilin := (λ x y, matrix.dot_product x y),
 bilin_add_left := by {apply matrix.add_dot_product,},
 bilin_add_right := by {apply matrix.dot_product_add,},
 bilin_smul_left := by {apply matrix.smul_dot_product,},
 bilin_smul_right := by {apply matrix.dot_product_smul,},
 }


/--
For two linearly independent vectors `v` and `w`, the property that
`u` is orthogonal to their span is equivalent to `u` being
orthogonal to `v` and `w`.
-/
lemma ortho_span_pair_iff
  (v w u : (fin 3 → (zmod p)) )
  (h : linear_independent (zmod p) ![v,w]) :
  u ∈ bilin_form.orthogonal (dotp p) (submodule.span (zmod p) {v,w})
  ↔ ((dotp p).bilin v u = 0 ∧ (dotp p).bilin w u = 0) :=
begin
  split,
  {intro susp,
   rw bilin_form.mem_orthogonal_iff at susp,
   simp_rw bilin_form.is_ortho_def at susp,
   split,
   {apply susp v,
    rw submodule.mem_span_insert,
    use (1 : zmod p),
    use (0 : fin 3 → zmod p),
    split,
    apply submodule.zero_mem _,
    simp only [add_zero, eq_self_iff_true, one_smul],
    },
    {apply susp w,
     rw [set.pair_comm v w],
     rw submodule.mem_span_insert,
     use (1 : zmod p), use (0 : fin 3 → zmod p),
     split,
     apply submodule.zero_mem _,
     simp only [add_zero, eq_self_iff_true, one_smul],
     },
  },
  {rintros ⟨ov,ow⟩,
   rw bilin_form.mem_orthogonal_iff,
   simp only [bilin_form.is_ortho_def],
   intros x xdef,
   apply submodule.span_induction xdef,
   -- generating vectors
   {intros y ydef,
    rw set.mem_insert_iff at ydef,
    cases ydef,
    rw ydef,
    apply ov,
    rw set.mem_singleton_iff at ydef,
    rw ydef,
    apply ow,},
   -- zero
   {apply bilin_form.zero_left,},
   -- add
   {intros y z yprop zprop,
    rw [bilin_form.add_left],
    rw [yprop, zprop],
    norm_num,},
   -- smul
   {intros a y yprop,
    simp only [bilin_form.smul_left, mul_eq_zero],
    right, exact yprop,},
  },
end

/-- The dot product is reflexive (crtl-click to see what it means)--/
lemma dotp_is_refl : (dotp p).is_refl :=
  by {apply bilin_form.is_symm.is_refl,
      intros x y,
      dsimp [dotp],
      apply matrix.dot_product_comm,}

/--
The dot product is nondegenerate
(there is no vector orthogonal to all vectors)
-/
lemma dotp_nondegenerate :
  (dotp p).orthogonal ⊤ = ⊥ :=
begin
  ext x,
  simp only [bilin_form.mem_orthogonal_iff, submodule.mem_bot],
  dsimp [bilin_form.is_ortho_def],
  dsimp [dotp],
  split,
  {intro forth,
    ext i,
    dsimp,
    specialize forth (pi.single i 1) (submodule.mem_top),
    rw matrix.dot_product_comm at forth,
    rw matrix.dot_product_single at forth,
    rw mul_one at forth,
    exact forth,
    },
  {intro back,
    intros y useless,
    rw back,
    apply matrix.dot_product_zero,},
end


/--
In (ℤ_p)^3, the dimension of the orthogonal complement
to the span of 2 linearly independent vectors is 1. 
-/
lemma dim_of_ortho
  (v w : (fin 3 → (zmod p)) )
  (h : linear_independent (zmod p) ![v,w]) :
  finite_dimensional.finrank (zmod p) ↥(bilin_form.orthogonal (dotp p) (submodule.span (zmod p) {v,w})) = 1 :=
begin
  have main_id := @bilin_form.finrank_add_finrank_orthogonal _ _ _ _ _ _ _ (submodule.span (zmod p) {v,w}) (dotp_is_refl p),
  rw finite_dimensional.finrank_fin_fun at main_id,
  have tec : {v,w} = (set.range ![v,w]) :=
    by {simp only [eq_self_iff_true, matrix.range_cons_cons_empty],},
  rw tec at main_id,
  rw finrank_span_eq_card h at main_id,
  rw ← tec at main_id,
  clear tec,
  rw (show fintype.card (fin (nat.succ 1)) = 2,
        by {dec_trivial,}) at main_id,
  rw dotp_nondegenerate at main_id,
  rw inf_bot_eq at main_id,
  simp only [add_zero, finrank_bot] at main_id,
  linarith,
end

/--
A rewrite lemma charcterising equality in the projective space
via linear independence of representatives.
-/
lemma rw_tec
  (v w : ℙ (zmod p) (fin 3 → zmod p)):
  v ≠ w ↔ linear_independent (zmod p) ![v.rep, w.rep] :=
begin
  have : (projectivization.rep ∘ ![v, w]) = ![v.rep , w.rep] :=
     by {ext i y,
         fin_cases i,
         dsimp, refl,
         dsimp, refl,},
  rw ← projectivization.independent_pair_iff_neq,
  rw projectivization.independent_iff,
  rw this,
end 


/--
The extremal graph we built is 4-cycle-free !
-/
lemma extremal_graph_c4_free :
  c4_free (extremal_graph p) :=
begin
  -- We use the charcterization in terms of common neighbours
  apply common_neighbors_c4_free (extremal_graph p),
  intros v w vnw,
  -- We then proceed by contradiction, so as to get
  -- common neighbours `a` and `b`
  by_contra' con,
  rw nat.lt_iff_add_one_le at con,
  norm_num at con,
  obtain ⟨a,⟨b,⟨meh,⟨ meeh, absub⟩⟩⟩⟩ := pair_of_two_le_card con,
  have adef := a.prop,
  have bdef := b.prop,
  simp_rw common_neighbors_eq at adef bdef,
  rw set.mem_inter_iff at adef bdef,
  -- We translate between neighbours and orthogonals
  simp_rw neighbor_extremal_graph at adef bdef,
  have bo : (b : ℙ (zmod p) (fin 3 → zmod p)).rep ∈ bilin_form.orthogonal (dotp p) (submodule.span (zmod p) {v.rep , w.rep}) :=
    by {rw ortho_span_pair_iff,
        dsimp [dotp],
        nth_rewrite 0 [matrix.dot_product_comm],
        nth_rewrite 1 [matrix.dot_product_comm],
        exact ⟨bdef.1.2,bdef.2.2⟩,
        exact (rw_tec p v w).mp vnw,
        },
  have ao : (a : ℙ (zmod p) (fin 3 → zmod p)).rep ∈ bilin_form.orthogonal (dotp p) (submodule.span (zmod p) {v.rep , w.rep}) :=
    by {rw ortho_span_pair_iff,
        dsimp [dotp],
        nth_rewrite 0 [matrix.dot_product_comm],
        nth_rewrite 1 [matrix.dot_product_comm],
        exact ⟨adef.1.2,adef.2.2⟩,
        exact (rw_tec p v w).mp vnw,
        },
  -- We recall the dimension of the orthogonal
  have dim_o := dim_of_ortho p v.rep w.rep ((rw_tec p v w).mp vnw),
  -- We recall the charcterization of 1-dimensional spaces 
  have dim_o_char := @finrank_eq_one_iff_of_nonzero' (zmod p) (↥((dotp p).orthogonal (submodule.span (zmod p) {v.rep, w.rep}))) _ _ _,
  -- We derive from it that `a` and `b` are dependent
  specialize dim_o_char ⟨(b.val).rep , bo⟩
    (by {intro con',
         rw subtype.ext_iff_val at con',
         dsimp at con',
         exact (projectivization.rep_nonzero (b.val)) con',
         }),
  rw dim_o_char at dim_o,
  obtain ⟨sc, eq⟩ := dim_o ⟨(a.val).rep , ao⟩,
  simp only [set_like.mk_smul_mk, subtype.mk_eq_mk, subtype.val_eq_coe] at eq,
  -- Yet, we recall that `a ≠ b` meant that they were independent 
  rw [ne.def, (not_iff_not.mpr subtype.ext_iff_val), ←ne.def ] at absub,
  rw (rw_tec p a.val b.val) at absub,
  rw linear_independent_fin2 at absub,
  simp only [matrix.head_cons, ne.def, matrix.cons_val_one, subtype.val_eq_coe] at absub,
  apply absub.2 sc,
  simp only [matrix.cons_val_zero],
  exact eq,
end 


-- To be continiued


