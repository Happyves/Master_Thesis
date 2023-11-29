
/-
Copyright (c) 2023 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import data.real.basic
import data.real.sqrt

import algebra.big_operators.basic
import algebra.big_operators.ring

import combinatorics.double_counting

import data.finset.basic
import data.finset.powerset
import data.finset.prod
import data.fintype.basic

import data.nat.basic

import data.set.basic

import tactic

open finset

open_locale classical


/-!

# Personal graph library and Reiman's theorem

This file contains the code referenced in the chpater
on the formalisation process of the Master thesis
this file belongs to.

Important content includes:

- `newGraph` :
      The graph structure for our graph library.

- `fourcycle` :
      The four vertex cycle for our graph library.

- `handshake_newGraph` :
      The handshake lemma for our graph library. 

- `is_graph_embed` :
      The property of a map of being a graph embedding
      for our library. 

- `max_edges_of_c4_free_Istvan_Reiman` :
      Reiman's theorem for our graph library. 

-/


-- A definition of graphs closer to the text-book definitions
structure newGraph (β : Type):=
(vertices : finset β )
(edges : finset (finset β ))
(is_graph : edges ⊆ vertices.powerset_len 2)

namespace newGraph

--How to define C₄ 
def fourcycle : newGraph nat :=
  {vertices := range 4,
  edges := list.to_finset [list.to_finset [0,1], list.to_finset [1,2],list.to_finset [2,3],list.to_finset [3,0]],
  is_graph := by {simp, intros e h,
                  repeat {cases h, rw h, rw mem_powerset_len, simp, intros v h', cases h',
                  simp at *, linarith, simp at *, dsimp [list.mem] at h',
                  cases h', linarith, exfalso, exact h',},
                  dsimp [list.mem] at h, exfalso, exact h,}}


#eval fourcycle.edges --one can easily check edges
#reduce fourcycle.edges.card --nice and computation friendly


--We now build Cₙ 
--Starting with a helper function you can ignore 
def helperCycle (n : nat) :=
   list.map (λ m, if m=(n-1) then [n-1,0] else [m,m.succ]) (list.range n)

#reduce helperCycle 6 --sanity check

--Takes in n and a proof that its bigger the 3 and outputs Cₙ 
def n_cycle (n : nat) (H : 3≤n): newGraph nat :=
  {vertices := range n,
  edges := list.to_finset (list.map list.to_finset (helperCycle n)),
  is_graph := by {intros e h, simp at *, rw mem_powerset_len,
                  rcases h with ⟨el,elH,coer⟩,
                  dsimp [helperCycle] at elH, simp at elH,
                  rcases elH with ⟨m,mln,more⟩,
                  by_cases c : m=n-1,
                  rw if_pos at more, rw [←coer, ←more], simp,
                  split, intros x h,
                  rw [finset.mem_insert] at h, cases h, simp, linarith,
                  rw mem_singleton at h, simp, linarith,
                  apply finset.card_insert_of_not_mem,
                  rw finset.mem_singleton,
                  by_contra,
                  have tmp : 1≤n := by {linarith,}, 
                  linarith,
                  exact c,
                  rw if_neg c at more, rw [←coer, ←more], simp, split,
                  intros x h,
                  rw [finset.mem_insert] at h, cases h, simp, linarith,
                  rw mem_singleton at h, simp,
                  have tmp : m.succ ≤n-1 := by {rw nat.succ_eq_add_one,
                                                apply lt_by_cases m (n-1),
                                                intro t, linarith,
                                                intro t, exfalso, exact c t,
                                                intro t, exfalso, 
                                                have tmp : 1≤n := by {linarith,},
                                                linarith,
                                                },
                  rw nat.succ_eq_add_one at *, rw h,
                  have myCurseItsMyFuckingCurse : 1≤n := by {linarith,}, linarith,
                  apply finset.card_insert_of_not_mem,
                  rw finset.mem_singleton,
                  exact (nat.succ_ne_self m).symm,}}

#reduce (n_cycle 10 (by {linarith})).edges.card --sanity check
#eval (n_cycle 10 (by {linarith})).edges 
#eval (n_cycle 1000 (by {linarith})).edges -- unfortunately 9000 failed

--Here's how we define vertex and edge neighbourhoods
def edge_neighborhood {β : Type} [decidable_eq β] (G : newGraph β)  (v : β) : finset (finset β ) :=
  ((G.edges).filter (λ e, v ∈ e))

def vert_neighborhood {β : Type} [decidable_eq β] (G : newGraph β)  (v : β) : finset ( β ) :=
  ((G.vertices).filter (λ u, ({u,v} : finset β) ∈ G.edges))

#eval edge_neighborhood fourcycle 2
#eval edge_neighborhood fourcycle 5
#eval vert_neighborhood fourcycle 2
#eval vert_neighborhood fourcycle 5

--The degree of a vertex
def vert_deg {β : Type} [decidable_eq β] (G : newGraph β)  (v : β) : nat :=
  (edge_neighborhood G v).card

#reduce vert_deg fourcycle 3 --again, computation friendly


--Incidence relations
def v_v_incidence_relation {β : Type} [decidable_eq β] (G : newGraph β) : β → β → Prop :=
  λ u v, if (list.to_finset [u,v] ∈ G.edges) then true else false

#reduce (v_v_incidence_relation fourcycle) 1 2
#reduce (v_v_incidence_relation fourcycle) 1 3

def v_e_incidence_relation {β : Type} [decidable_eq β] : β → finset β → Prop :=
  λ v e, if (v ∈ e) then true else false --doesn't require a graph

#reduce v_e_incidence_relation 1 {1,2}

--Some tecnicallities leading up to the handshake lemma 

lemma inci_edges {β : Type} [decidable_eq β] (G : newGraph β) (e : finset β ) (e_edge : e ∈ G.edges): 
           finset.bipartite_below v_e_incidence_relation (G.vertices) e = e :=
  by {ext v, split,
      rw mem_bipartite_below, rintro ⟨v_vert, inci⟩,
      dsimp [v_e_incidence_relation] at inci, by_contra k, rw if_neg k at inci, exact inci,
      intro v_e, rw mem_bipartite_below, split,
      have tec : e∈ G.vertices.powerset_len 2 := by {exact G.is_graph e_edge,},
      rw mem_powerset_len at tec, exact tec.1 v_e,
      dsimp [v_e_incidence_relation], rw if_pos v_e, trivial,}

lemma inci_vert {β : Type} [decidable_eq β] (G : newGraph β) (v : β ) (v_vert : v ∈ G.vertices): 
           finset.bipartite_above v_e_incidence_relation (G.edges) v = edge_neighborhood G v :=
  by {ext e, split,
      rw mem_bipartite_above, rintro ⟨e_edge, inci⟩,
      dsimp [v_e_incidence_relation] at inci, dsimp [edge_neighborhood],
      rw mem_filter, split, exact e_edge, by_contra k, rw if_neg k at inci, exact inci,
      intro e_nei, dsimp [edge_neighborhood] at e_nei, rw mem_filter at e_nei,
      rw mem_bipartite_above, split, exact e_nei.1, dsimp [v_e_incidence_relation],
      rw if_pos e_nei.2, trivial,}

lemma edges_size_2 {β : Type} [decidable_eq β] (G : newGraph β) (e : finset β ) (e_edge : e ∈ G.edges) :
                   e.card =2 := by {have : e ∈ G.vertices.powerset_len 2 := G.is_graph e_edge, rw mem_powerset_len at this, exact this.2,}

open_locale big_operators

--Handshake lemma. Uses combinatorics.double_counting
theorem handshake_newGraph {β : Type} [decidable_eq β] (G : newGraph β) :
        2*(G.edges.card) = ∑ v in G.vertices, (vert_deg G v) :=
  by {rw card_eq_sum_ones, rw mul_sum, simp_rw [show 2*1 = 2, by {norm_num}],
      calc
      ∑ (x : finset β) in G.edges, 2 = ∑ (x : finset β) in G.edges, x.card : by {rw sum_congr, refl, intros e e_edge, exact (edges_size_2 G e e_edge).symm,}
      ... = ∑ (x : finset β) in G.edges, (finset.bipartite_below v_e_incidence_relation (G.vertices) x).card : by {rw sum_congr, refl, intros e e_edge, congr, exact (inci_edges G e e_edge).symm,}
      ... = ∑ (x : β) in G.vertices, (finset.bipartite_above v_e_incidence_relation (G.edges) x).card : by {apply sum_card_bipartite_above_eq_sum_card_bipartite_below,}
      ... = ∑ (x : β) in G.vertices, vert_deg G x : by {rw sum_congr, refl, intros v v_vert, dsimp [vert_deg], congr, exact inci_vert G v v_vert,},
      }


--Graph embeddings: specified by a function mapping vertices of one graph to those of another
-- the conditions are that the map is injective, and edges of the antecedant graph are edges in the image graph
def is_graph_embed {α β : Type} [decidable_eq α] [decidable_eq β] (H : newGraph α ) (G : newGraph β ) (f : α → β ): Prop :=
  (∀v ∈ H.vertices, f v ∈G.vertices ) ∧ (∀v u, v∈ H.vertices → u ∈ H.vertices → (f v = f u) → (v = u) )
  ∧ (∀v u, v∈ H.vertices → u ∈ H.vertices → list.to_finset [u,v] ∈ H.edges → list.to_finset [f u, f v] ∈ G.edges) 

--Extending and deleting vertices and edges in graphs.
def graph_extend {α : Type} [decidable_eq α] (G : newGraph α )
                 (V : finset α) (E : finset (finset α))
                 (P : E ⊆ powerset_len 2 (V ∪ G.vertices)) : newGraph α :=
  {vertices := V ∪ G.vertices,
   edges := E ∪ G.edges,
   is_graph := by {intro e, simp, 
                   intro h, cases h with hV hG,
                   exact P hV,
                   rw mem_powerset_len, split,
                   have inter : e ⊆ G.vertices :=
                    by {exact (mem_powerset_len.mp (G.is_graph hG)).1,},
                   apply subset.trans inter, exact (subset_union_right V G.vertices),
                   exact (mem_powerset_len.mp (G.is_graph hG)).2,
                   }
  }

def graph_delete {α : Type} [decidable_eq α] (G : newGraph α )
                 (V : finset α) (E : finset (finset α))
                 (P : E ⊆ powerset_len 2 (V ∪ G.vertices)) : newGraph α :=
  {vertices := G.vertices \ V,
   edges := G.edges \ (E ∪ (G.edges.filter (λ e, (∃v∈e,v∈V)))),
   is_graph := by {intro e, simp, push_neg,
                   intro e_edge, rintro ⟨enE, ve⟩, specialize ve e_edge,
                   rw mem_powerset_len, split,
                   intros u ue, simp, split,
                   exact ((mem_powerset_len.mp (G.is_graph e_edge)).1 ue),
                   exact ve u ue,
                   exact (mem_powerset_len.mp (G.is_graph e_edge)).2,},
   }

--sanity checks on C₄
#eval (graph_extend fourcycle (∅) ({{0,2}}) --eval displayed on this line
      (by {simp, rw mem_powerset_len, simp, unfold fourcycle, simp, intros v h', cases h',
       simp at *, linarith, simp at *, dsimp [list.mem] at h',
      cases h', linarith, exfalso, exact h',})
      ).edges

#eval (graph_delete fourcycle ({2}) (∅) --eval displayed on this line
      (by {simp,})
      ).edges

--some special graphs
def my_empty_graph (α : Type) [decidable_eq α] : newGraph α :=
{vertices := ∅,
 edges := ∅,
 is_graph := by {simp,}}  


def one_vert_graph : newGraph nat :=
{vertices := singleton 1,
 edges := ∅,
 is_graph := by {exact (powerset_len 2 {1}).empty_subset}}


#check classical.some
#check classical.some_spec

lemma other_end_prop {β : Type} [decidable_eq β] (G : newGraph β)  (v : β) (e : finset β )
  (hv : v ∈ e ) (he : e ∈ G.edges) : ∃ u : β, u ∈ e.erase v :=
  by {replace he := G.is_graph he, rw mem_powerset_len at he,
        have : 0 < (e.erase v).card :=
          by {rw card_erase_of_mem hv, rw he.2, norm_num,},
        rw finset.card_pos at this, apply this,}

noncomputable
def other_end {β : Type} [decidable_eq β] (G : newGraph β)  (v : β) (e : finset β )
  (hv : v ∈ e ) (he : e ∈ G.edges) : β :=
  classical.some (other_end_prop G v e hv he)

lemma other_end_is_end {β : Type} [decidable_eq β] (G : newGraph β)  (v : β) (e : finset β )
  (hv : v ∈ e ) (he : e ∈ G.edges) : other_end G v e hv he ∈ e :=
by {rw other_end,
    have : _ := classical.some_spec (other_end_prop G v e hv he),
    exact (erase_subset v e) this,}

lemma other_end_is_differerent {β : Type} [decidable_eq β] (G : newGraph β)  (v : β) (e : finset β )
  (hv : v ∈ e ) (he : e ∈ G.edges) : other_end G v e hv he ≠ v  :=
by {rw other_end,
    have : _ := classical.some_spec (other_end_prop G v e hv he),
    intro con, rw con at this,
    exact false.elim ((not_mem_erase v e) this),} 

lemma other_end_is_vert {β : Type} [decidable_eq β] (G : newGraph β)  (v : β) (e : finset β )
  (hv : v ∈ e ) (he : e ∈ G.edges) : other_end G v e hv he ∈ G.vertices :=
by {--replace he := (G.is_graph he), --fails, but worked for other_end_prop
    rw other_end,
    have : _ := classical.some_spec (other_end_prop G v e hv he),
    have that : _ := G.is_graph he,
    replace this := ((erase_subset v e) this),
    rw mem_powerset_len at that,
    apply that.1 this,}

lemma other_end_end_edge {β : Type} [decidable_eq β] (G : newGraph β)  (v : β) (e : finset β )
  (hv : v ∈ e ) (he : e ∈ G.edges) : {other_end G v e hv he , v} = e :=
by {--rw other_end,
    --have : _ := classical.some_spec (other_end_prop G v e hv he),
    ext w, split,
    intro explicit, rw [finset.mem_insert] at explicit, cases explicit,
    rw explicit, apply other_end_is_end, rw mem_singleton at explicit, rw ← explicit at hv, exact hv,
    intro we, by_contra' con,
    have facts_1 : _ := (G.is_graph he), rw mem_powerset_len at facts_1,
    have facts_2 : _ := other_end_is_differerent G v e hv he,
    have obs1 : ({w,other_end G v e hv he, v} : finset β).card = 3 :=
      by {rw card_insert_of_not_mem _, rw card_insert_of_not_mem _,
          simp,
          simp, apply facts_2,
          exact con,},
    have obs2 : ({w,other_end G v e hv he, v} : finset β) ⊆ e := 
      by {intros x xdef,
          rw [finset.mem_insert] at xdef, cases xdef,  rw xdef, exact we,
          rw [finset.mem_insert] at xdef, cases xdef,  rw xdef, apply other_end_is_end,
          rw mem_singleton at xdef, rw xdef, exact hv,},
    have obs3 : ({w,other_end G v e hv he, v} : finset β).card ≤ e.card := card_le_of_subset obs2,
    rw facts_1.2 at obs3, rw obs1 at obs3,
    linarith, 
    } 

lemma vert_deg_neighbourhood {β : Type} [decidable_eq β] (G : newGraph β)  (v : β) :
  (edge_neighborhood G v).card = (vert_neighborhood G v).card :=
by {simp only [edge_neighborhood, vert_neighborhood],
    apply finset.card_congr
      (λ (e : finset β), λ (edef : e ∈ filter (has_mem.mem v) G.edges),
          other_end G v e (show v∈e, by {rw mem_filter at edef, exact edef.2,}) (show e∈G.edges, by {apply (filter_subset (has_mem.mem v) G.edges) edef,} )),
    --map
    {intros e edef, simp, split, apply other_end_is_vert, rw other_end_end_edge,
     rw mem_filter at edef, exact edef.1,},
    --inj
    {intros e1 e2 e1def e2def eq, simp at eq,
     rw mem_filter at e1def, rw mem_filter at e2def, rcases e1def with ⟨e1e,ve1⟩, rcases e2def with ⟨e2e,ve2⟩,
     rw ← other_end_end_edge G v e1 ve1 e1e, rw ← other_end_end_edge G v e2 ve2 e2e,
     rw eq,
     },
     {intros p pdef,
      use ({p,v} : finset β),
      apply exists.intro,
      {simp, rw mem_filter at pdef,
      have : _ := other_end_is_end G v ({p,v} : finset β) (by { rw mem_insert, right, simp,}) (by { exact pdef.2,}),
      rw mem_insert at this, cases this, exact this, simp at this,
      have that : _ := ((other_end_is_differerent G v ({p,v} : finset β) (by { rw mem_insert, right, simp,}) (by { exact pdef.2,})) this),
      by_contra, --exfalso fails and I have no clue why XD
      apply that,},
      rw mem_filter at *, split, exact pdef.2,
      rw mem_insert, right, simp,}
    }


end newGraph

open newGraph

#check handshake_newGraph

variables {α : Type} [decidable_eq α]



lemma pair_of_two_le_card {s : finset α} (h : 2 ≤ s.card) :
  ∃ a, ∃ b, (a∈s ∧ b∈s ∧ a≠b) :=
by {have first : 0 < s.card := by {linarith,},
    rw finset.card_pos at first,
    obtain ⟨fst,fst_def⟩ : _ :=  first,
    use fst,
    have second : 0 < (s.erase fst).card :=
      by {have :_ := finset.card_erase_add_one fst_def,
           rw ← this at h, linarith,},
    rw finset.card_pos at second,
    obtain ⟨snd,snd_def⟩ : _ :=  second,
    use snd,
    split, exact fst_def,
    split, apply (finset.erase_subset fst s) snd_def,
    intro con, rw ← con at snd_def, apply (finset.not_mem_erase fst s) snd_def,}  



def c4_free (G : newGraph α): Prop :=
  ¬ ∃ f : ℕ → α, (is_graph_embed fourcycle G f)  


def embed_aux (a v b w : α) ( n : ℕ): α := 
match n with
| 0 := a
| 1 := v
| 2 := b
| 3 := w
| _ := a --dummy assignement
end

lemma embed_aux_inj (a v b w : α) (n m : ℕ) --thanks Bhavik
      (ndef: n ∈ finset.range 4) (mdef: m ∈ finset.range 4)
      (embedeq: embed_aux a v b w n = embed_aux a v b w m)
      (anv : a≠v) (anb : a≠b) (anw : a≠w) (vnb : v≠b) (vnw : v≠w) (bnw : b≠w) :
  n = m :=
by fin_cases ndef; fin_cases mdef; { simp only [embed_aux] at embedeq, cc }



lemma neq_of_edge {G : newGraph α} {a b : α} (h : {a,b} ∈ G.edges ) : a ≠ b :=
by {replace h := G.is_graph h,
    rw finset.mem_powerset_len at h,
    by_contra con, rw con at h, simp at h, exact h,} 


lemma c4_free_common_neighbours (G : newGraph α) (hG : c4_free G)
  (v w : α) (vdef : v ∈ G.vertices) (wdef : w ∈ G.vertices) (vnu : v ≠ w) :
  ((vert_neighborhood G v) ∩ (vert_neighborhood G w)).card ≤ 1 :=
begin
  by_contra' pair_o_vert,
  rw ← nat.add_one_le_iff at pair_o_vert, norm_num at pair_o_vert,
  replace pair_o_vert := pair_of_two_le_card pair_o_vert,
  rcases pair_o_vert with ⟨a,⟨b,⟨adef,⟨bdef,anb⟩⟩ ⟩ ⟩,
  simp [vert_neighborhood] at adef, simp [vert_neighborhood] at bdef,
  apply hG,
  let embed := embed_aux a v b w,
  use embed, dsimp [is_graph_embed], split,
  {intros u udef, dsimp [fourcycle] at udef,
   cases udef, rw udef, simp [embed, embed_aux], exact adef.1.1,
   cases udef, simp at udef, rw udef, simp [embed, embed_aux], exact vdef,
   cases udef, simp at udef, rw udef, simp [embed, embed_aux], exact bdef.1.1,
   cases udef, simp at udef, rw udef, simp [embed, embed_aux], exact wdef,
   exfalso, exact (list.mem_nil_iff u).mp udef,},
  split,
  {intros n m ndef mdef embedeq,
   dsimp [fourcycle] at ndef, dsimp [fourcycle] at mdef, dsimp [embed] at embedeq,
   have anv : _ := neq_of_edge adef.1.2,
   have anw : _ := neq_of_edge adef.2.2,
   have bnv : _ := neq_of_edge bdef.1.2,
   have bnw : _ := neq_of_edge bdef.2.2,
   apply embed_aux_inj a v b w n m ndef mdef embedeq,
   repeat {assumption <|> {apply ne.symm, assumption}},},
  {intros x y xdef ydef h,
   let ax := x, let ay := y, 
   simp only [is_lawful_singleton.insert_emptyc_eq, list.to_finset_nil, list.to_finset_cons, embed, embed_aux],
   fin_cases xdef; fin_cases ydef; {  {have : [ay,ax].to_finset ∉ fourcycle.edges := by { dsimp [ax, ay], dec_trivial,}, dsimp [ax, ay] at this, apply false.elim ( this h),}
                                    <|> {rw finset.pair_comm, try {apply adef.1.2}, try {apply adef.2.2}, try {apply bdef.1.2}, try {apply bdef.2.2},}
                                    <|> {try {apply adef.1.2}, try {apply adef.2.2}, try {apply bdef.1.2}, try {apply bdef.2.2},},}
   
   }
end

example : 4 ∉ ({1,2,3} : finset ℕ) := by {simp?,} 
example : ({4,1} : finset ℕ) ∉ ({({2,1} : finset ℕ),({5,1} : finset ℕ)} : finset (finset ℕ)) :=
  by {dec_trivial,} 

open_locale classical 

def double_counting_rel (G : newGraph α ) (u : α) (e : finset α ) : Prop :=
   (u ∈ G.vertices) ∧ (e ∈ finset.powerset_len 2 ((G.vertices).erase u)) ∧ 
   (∀ v, v ∈ e → u ∈ vert_neighborhood G v)

#check decidable_pred
#check decidable


open finset

lemma double_count_above (G : newGraph α ) (u : α) (hu : u ∈ G.vertices) :
   ((finset.bipartite_above (double_counting_rel G) (finset.powerset_len 2 ((G.vertices)))) u ).card = (vert_deg G u).choose 2 :=
begin
  simp [finset.bipartite_above, vert_deg], rw vert_deg_neighbourhood,
  rw ← finset.card_powerset_len 2 (vert_neighborhood G u),
  congr,
  ext x, split,
  {intro xfil, simp [mem_filter, double_counting_rel] at xfil,
  simp [vert_neighborhood] at *, simp [mem_powerset_len] at *, split,
  swap, exact xfil.1.2,
  intros v vx, rw mem_filter, rw pair_comm, split,
  --exact (erase_subset u G.vertices) (xfil.1.1 vx), exact (xfil.2.2.2 v vx).2,
  exact xfil.1.1 vx, exact (xfil.2.2.2 v vx).2,
  },
  intro xpow, simp [mem_filter, double_counting_rel, vert_neighborhood, mem_powerset_len] at *,
  split, split, swap, exact xpow.2, apply subset_trans xpow.1,
  apply filter_subset,
  -- {rw subset_erase, split, apply filter_subset, simp, intro useless,
  --  intro con, replace con := G.is_graph con, rw mem_powerset_len at con, simp at con, exact con,},
  split, exact hu,
  split, split, swap, exact xpow.2, apply subset_trans xpow.1,
  {rw subset_erase, split, apply filter_subset, simp, intro useless,
   intro con, replace con := G.is_graph con, rw mem_powerset_len at con, simp at con, exact con,},
  intros v vx, split, exact hu,
  have : _ := xpow.1 vx, rw mem_filter at this, rw pair_comm, exact this.2,
end


lemma double_count_below (G : newGraph α ) (hG : c4_free G)
   (v w : α) (hv : v ∈ G.vertices) (hw : w ∈ G.vertices) (vnw : v ≠ w ):
   ((finset.bipartite_below (double_counting_rel G) (((G.vertices)))) ({v,w} : finset α) ).card ≤ 1 :=
begin
  simp [finset.bipartite_below, double_counting_rel],
  apply le_trans _ (c4_free_common_neighbours G hG v w hv hw vnw),
  apply card_le_of_subset,
  intros u udef, rw mem_filter at udef, rw mem_inter, exact udef.2.2.2,
end 



lemma pair_of_card_ge_two {β : Type} {s : finset β} (h : s.card = 2) :
      ∃ a, ∃ b, (a ≠ b) ∧ (s = {a, b}) :=
by {have : 0 <s.card := by {linarith,},
    rw card_pos at this, rcases this with ⟨a, adef⟩,
    use a,
    have : 0 <(s.erase a).card := by {rw card_erase_of_mem adef, rw h, norm_num,},
    rw card_pos at this, rcases this with ⟨b, bdef⟩,
    use b,
    split,
    intro con, rw con at bdef, exact (not_mem_erase b s) bdef,
    ext x, split, intro xs, by_contra con,
    have one : (insert x ({a,b} : finset β) ).card = 3 :=
      by {rw card_insert_of_not_mem con,
          rw card_insert_of_not_mem _,
          simp,
          intro con, rw mem_singleton at con, rw con at bdef, exact (not_mem_erase b s) bdef,},
    have two : (insert x ({a,b} : finset β) ) ⊆ s :=
      by {replace bdef := (erase_subset a s ) bdef,
          intros y ydef,
          repeat {rw mem_insert at ydef, cases ydef, rw ydef, assumption,},
          rw mem_singleton at ydef, rw ydef, assumption,},
    replace two := card_le_of_subset two, rw one at two, linarith,
    intro xab,
    rw mem_insert at xab, cases xab, rw xab, exact adef,
    rw mem_singleton at xab, cases xab, rw xab, exact (erase_subset a s ) bdef,}

open_locale big_operators

lemma double_count_below_bound (G : newGraph α ) (hG : c4_free G):
  ∑ p in (finset.powerset_len 2 G.vertices), ((finset.bipartite_below (double_counting_rel G) (((G.vertices)))) p ).card
  ≤ ((G.vertices).card).choose 2 :=
begin
  rw ← finset.card_powerset_len 2 G.vertices,
  rw card_eq_sum_ones,
  apply sum_le_sum,
  intros p pdef,
  --apply double_count_below G,
  rw mem_powerset_len at pdef,
  obtain ⟨a,⟨b,⟨anb,eq⟩⟩⟩  : _ := pair_of_card_ge_two pdef.2,
  rw eq,
  have avert : a ∈ G.vertices := by { apply pdef.1, rw eq, rw mem_insert, left, refl,},
  have bvert : b ∈ G.vertices := by { apply pdef.1, rw eq, rw mem_insert, right, rw mem_singleton,},
  convert double_count_below G hG a b avert bvert anb, --apply fails
end

#check sum_card_bipartite_above_eq_sum_card_bipartite_below


lemma first_ineq (G : newGraph α ) (hG : c4_free G):
  ∑ u in G.vertices, (vert_deg G u).choose 2 ≤ ((G.vertices).card).choose 2 :=
begin
  have : _ := @sum_card_bipartite_above_eq_sum_card_bipartite_below _ _ (double_counting_rel G) G.vertices (finset.powerset_len 2 G.vertices) _,
  have pain : ∑ (a : α) in G.vertices, (bipartite_above (double_counting_rel G) (powerset_len 2 G.vertices) a).card = ∑ u in G.vertices, (vert_deg G u).choose 2 :=
    by {apply sum_congr, refl, intros x xdef, apply double_count_above G x xdef,},
  rw ← pain, rw this,
  apply double_count_below_bound G hG,
end 

#check nat.choose_two_right
#check nat.mul_sub_left_distrib
#check sum_sub_distrib
--example : subtraction_comm_monoid ℕ := infer_instance

lemma nat.sum_sub_distrib  {α : Type} (s : finset α) (f g : α → ℕ)
      (h : ∀ i, g i ≤ f i): -- i∈ s would be better but then a different induction is necessary
      ∑ i in s, (f i - g i) = (∑ i in s, f i )- (∑ i in s, g i)  :=
  by {--library_search,
      apply finset.induction_on s,
      simp,
      intros a s ans ih,
      rw [sum_insert,sum_insert, sum_insert],
      rw ih, repeat {swap, exact ans,},
      apply tsub_add_tsub_comm,
      exact h a,
      apply sum_le_sum,
      intros i is, exact h i,}

#check tsub_add_eq_add_tsub
#check nat.add_sub_assoc

lemma nat.add_sub_add_eq_sub_add_sub (a b c d : ℕ) (h1 : a≤b) (h2 : c≤d):
  (b - a) + (d - c) = (b + d) - (a + c) :=
  by {exact tsub_add_tsub_comm h1 h2,}


lemma tec_stuff (n : ℕ) : 2*((n*(n-1))/2) = n*(n-1) :=
  by {nth_rewrite 1 ← nat.mod_add_div (n*(n-1)) 2,
      rw self_eq_add_left,
      --library_search,
      rw nat.mul_mod,
      have : (n % 2) * ((n - 1) % 2) = 0 :=
        by {rw mul_eq_zero,
            induction n with n ih,
            left, dec_trivial,
            cases ih,
            right, rw nat.succ_sub_one, exact ih,
            by_cases q : n = 0,
            rw q, dec_trivial,
            rw ← ne.def at q, rw ← nat.one_le_iff_ne_zero at q,
            left,
            have id : n.succ = (n - 1) + 2 :=
              by {rw nat.succ_eq_add_one, linarith,},
            rw id,
            rw nat.add_mod, 
            rw ih,
            dec_trivial,
            },
      rw this,
      dec_trivial,}


lemma mathlib_is_a_desert (n m k: ℕ) : n≤m → (m - n ≤ k ↔ m ≤ k + n)  :=
  by {--library_search,
      intro h,
      nth_rewrite 1 ← nat.sub_add_cancel h,
      simp,} 

lemma first_ineq_rw (G : newGraph α ) (hG : c4_free G):
  ∑ u in G.vertices, (vert_deg G u)^2 ≤ (G.vertices.card)*(G.vertices.card - 1) + ∑ u in G.vertices, (vert_deg G u) :=
begin
  have : _ := first_ineq G hG,
  rw [nat.choose_two_right] at this,
  simp_rw [nat.choose_two_right] at this,
  have that : monotone (λ x, 2*x) := 
    by {simp [monotone],},
  apply_fun (λ x, 2*x) at this using that,
  rw mul_sum at this,
  rw tec_stuff G.vertices.card at this,
  simp_rw [tec_stuff] at this,
  rw nat.mul_sub_left_distrib at this,
  simp_rw [nat.mul_sub_left_distrib] at this,
  simp_rw [← pow_two, mul_one] at this,
  
  have tec : ∀ (i : α), vert_deg G i ≤ vert_deg G i ^ 2 :=
    by {intro i,
        by_cases q : (vert_deg G i) = 0,
        rw q, dec_trivial,
        nth_rewrite 0 [← mul_one (vert_deg G i)], rw pow_two,
        rw mul_le_mul_left,
        rw nat.one_le_iff_ne_zero, apply q,
        rw nat.lt_iff_add_one_le, rw zero_add, rw nat.one_le_iff_ne_zero, apply q,},
  rw nat.sum_sub_distrib at this,
  swap, exact tec,
  rw mathlib_is_a_desert _ at this,
  rw nat.mul_sub_left_distrib, rw [←pow_two,mul_one], exact this,  
  apply sum_le_sum, intros i idef, exact tec i,
end

  --Cauchy-Schwartz is implemented as norm_inner_le_norm but it requires the ring to be ℝ or ℂ ...
lemma Cauchy_Schwartz_int (v w : α → ℤ) (s : finset α):
  (∑ i in s, (v i)*(w i))^2 ≤ (∑ i in s, (v i)^2)*(∑ i in s, (w i)^2) :=
begin
  have start :  0 ≤ (∑ i in s, (∑ j in s, ((v i)*(w j) - (v j)*(w i))^2 )) :=
    by {apply sum_nonneg, intros i idef, apply sum_nonneg, intros j jdef, apply sq_nonneg,},
  simp_rw sub_sq at start,
  have rw_1 : ∀ i, (∑ j in s, (((v i)*(w j))^2 - 2*((v i)*(w j))*((v j)*(w i)) + ((v j)*(w i))^2 )) =
                   ((v i)^2)*(∑ j in s,(w j)^2) - 2*((v i)*(w i))*(∑ j in s,((v j)*(w j))) + ((w i)^2)*(∑ j in s,(v j)^2) :=
    by {intro i, rw sum_add_distrib, rw sum_sub_distrib, simp_rw mul_pow,
        rw ←mul_sum, rw ←sum_mul, nth_rewrite 1 mul_comm, --bizare order...
        have micro : ∀ j, 2*((v i)*(w j))*((v j)*(w i)) = (2*((v i)*(w i)))*((v j)*(w j)) :=
          by {intro j, ring,},
        simp_rw [micro], rw ←mul_sum,},
  simp_rw [rw_1] at start, clear rw_1,
  rw sum_add_distrib at start, rw sum_sub_distrib at start,
  rw [←sum_mul, ←sum_mul, ←sum_mul] at start, rw ←mul_sum at start,
  linarith, --flex
end

lemma Cauchy_Schwartz_in_action (G : newGraph α):
  ((∑ u in G.vertices, (vert_deg G u))^2 : ℤ)  ≤ G.vertices.card * ∑ u in G.vertices, (vert_deg G u)^2 :=
by {have : _ := Cauchy_Schwartz_int (λ u, (vert_deg G u)) (λu, (1 : ℤ)) G.vertices,
    simp_rw [mul_pow, one_pow, mul_one] at this,
    simp_rw [card_eq_sum_ones G.vertices], rw mul_comm, --exact this, --coersion works fiiine
    push_cast, rw zero_add, exact this,}

lemma second_ineq (G : newGraph α ) (hG : c4_free G) :
  ((∑ u in G.vertices, (vert_deg G u))^2 : ℤ) ≤ (G.vertices.card^2)*(G.vertices.card - 1) + (G.vertices.card)*(∑ u in G.vertices, (vert_deg G u)) :=
begin
  apply le_trans (Cauchy_Schwartz_in_action G),
  rw pow_two, rw mul_assoc, rw ←mul_add,
  by_cases q : 0 < G.vertices.card,
  rw mul_le_mul_left, swap 2, rw nat.cast_pos, exact q,
  have : _ := first_ineq_rw G hG,
  rw ← @nat.cast_le ℤ _ _ _ _ at this,
  push_cast at this,
  exact this,
  have : G.vertices.card = 0 := by {linarith,},
  rw this,
  simp,
end

#check real.sqrt (1 : ℝ )

example (x y: ℝ) (h : x^2 ≤ y) : x ≤ real.sqrt y := by {exact real.le_sqrt_of_sq_le h,}

lemma third_ineq (G : newGraph α ) (hG : c4_free G) :
  (4*(G.edges.card)^2 : ℝ) ≤ (G.vertices.card^2)*(G.vertices.card - 1) + (G.vertices.card)*2*(G.edges.card) :=
begin
  rw (show (4 : ℝ)  = 2^2, by {norm_num1,}),
  rw ← mul_pow, 
  rw mul_assoc,
  have : _ := handshake_newGraph G,
  apply_fun (λ x, (x : ℝ)) at this,
  simp at this, rw this, clear this,
  have : _ :=  second_ineq G hG,
  have that :monotone (λ x : ℤ, (x : ℝ)) := by {simp [monotone],},
  apply_fun (λ x, (x : ℝ)) at this using that,
  simp at this, exact this,
end

#check int.floor
#check ⌊(1 : ℝ)⌋
--#eval ⌊(1 : ℝ)⌋
#check int.le_floor

theorem max_edges_of_c4_free_Istvan_Reiman (G : newGraph α ) (hG : c4_free G) :
  ((G.edges.card) : ℤ) ≤ ⌊(G.vertices.card / 4 : ℝ)*(1 + real.sqrt (4*G.vertices.card - 3))⌋ :=
begin
  rw int.le_floor,
  simp,
  --cancel_denoms,
  rw mul_add, rw mul_one,
  apply le_add_of_sub_left_le,
  --rw ← (mul_le_mul_left (show 0<2, by {norm_num,})),
  have ineq : _ := third_ineq G hG,
  have canonic : (4 : ℝ)*((G.edges.card - (G.vertices.card / 4))^2) ≤ ((((G.vertices.card)^2)/4)*(1+((4*G.vertices.card) -4))) :=
    by {rw pow_two, rw sub_mul, rw mul_sub, rw mul_sub, rw ← pow_two,
        cancel_denoms, simp_rw mul_assoc, rw ← mul_add,
        rw mul_le_mul_left (show 0<(4: ℝ), by {norm_num}),
        cancel_denoms, ring,
        have one : (((4 * ↑(G.vertices.card)) - 4) : ℝ) = 4*(↑(G.vertices.card) - 1) :=
          by {rw mul_sub, rw mul_one,},
        rw one, clear one,
        rw add_mul,
        rw [show (16 : ℝ) = 4*4, by {norm_num} ],
        rw [show (8 : ℝ) = 4*2, by {norm_num} ],
        simp_rw [mul_assoc],
        rw ←mul_add,
        rw mul_le_mul_left (show 0<(4: ℝ), by {norm_num}),
        rw ← pow_two, rw ←mul_assoc, nth_rewrite 1 mul_comm, nth_rewrite 2 mul_comm, 
        rw ← mul_assoc, exact ineq,},
  rw ← (mul_le_mul_left (show 0<(2: ℝ), by {norm_num})),
  nth_rewrite 0 [show (4 : ℝ) = 2^2, by {norm_num} ] at canonic,
  rw ← mul_pow at canonic,
  replace canonic := real.le_sqrt_of_sq_le canonic,
  rw real.sqrt_mul at canonic,
  rw ← mul_assoc,
  have one : 2 * (↑(G.vertices.card) / 4) = real.sqrt ((↑(G.vertices.card)^2) / 4) :=
    by {rw real.sqrt_div, rw real.sqrt_sq _, rw mul_div_left_comm,
        rw [show (2/4 : ℝ) = 1/2, by {norm_num} ],
        rw [show (4: ℝ) = 2*2, by {norm_num} ],
        rw real.sqrt_mul_self (show (0: ℝ) ≤ 2, by {norm_num}),
        ring,
        apply nat.cast_nonneg,
        apply sq_nonneg,},
  rw one,
  have two : (1 : ℝ) + (4 * ↑(G.vertices.card) - 4) = 4 * ↑(G.vertices.card) - 3 :=
    by {linarith,},
  simp_rw ← two,
  exact canonic,
  apply div_nonneg,
  apply sq_nonneg,
  norm_num,
end


