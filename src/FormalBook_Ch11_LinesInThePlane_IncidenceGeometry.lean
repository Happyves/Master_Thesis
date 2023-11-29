
/-
Copyright (c) 2023 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import tactic
import analysis.inner_product_space.basic
import analysis.inner_product_space.projection
import FormalBook_Ch11_LinesInThePlane_SylvesterGallai
import data.finset.card
import combinatorics.simple_graph.subgraph
import combinatorics.simple_graph.clique

/-!
# Lines in the plane and decompositions of graphs : 2 theorems and a graph decomposition

This file is part of a Master thesis project of formalizing some proofs from
"Proofs from THE BOOK" (5th ed.) by Martin Aigner and Günter M. Ziegler. 

We refer to chapter 11: "Pigeon-hole and double counting".
In this file, we formalize the theorems refered to as 
"Theorem 2" and "Theorem 3", as well as the first
graph decomposition theorem, in the corresponding chapter
of the book.


## Structure

- `theorem_2` :
      Attributed to Erdös and de Bruijn.
      If a finite set of points aren't aligned, then the number
      of lines passing through pairs of these points is greater
      then the number of points.

- `line_set` :
      Our definition of the set of lines of a point set for `theorem_2`

- `theorem_3` :
      Attributed to Motzkin or Conway.
      Generalises `theorem_2` to more abstract incidence geometries.

- `clique_decomposition` and `clique_decomposition'` :
      If we decompose a complete graph Kₙ into m cliques different
      from  Kₙ, such that every edge is in a unique clique, then m ≥ n.
      There are two versions, with two different notions of "clique"

-/

/- We work in the same context as in the Sylvester-Gallai file-/
variables {E : Type} [_inst_1 : normed_add_comm_group E] [_inst_2 : inner_product_space ℝ E] [_inst_3 : complete_space E]


open_locale classical


/--
The set of lines passing through pairs of distinct points of
a finite set of points `P`.
-/
noncomputable
def line_set (P : finset E) :=
  finset.image
    (λ p : ↥P × ↥P, line (p.1 : E) (p.2 : E)) -- `.val` failed
    (finset.filter
      (λ p : ↥P × ↥P, p.1 ≠ p.2)
      finset.univ)


/--
If the line passing through `u ∈ P` and `v ∈ P` contains no other
points of `P`, then the set of lines of `P\u` is less then that
of `P`
-/
lemma list_set_lemma
  (P : finset E)
  (u v: E) (hu : u ∈ P) (hv : v ∈ P) (unv : u ≠ v)
  (uv_prop: ∀ (p : E), p ∈ P → p ≠ u → p ≠ v → p ∉ line u v):
  (line_set (P.erase u)).card < (line_set P).card :=
begin
  apply finset.card_lt_card,
  -- We show that erasing `u` causes line `line u v` 
  -- to be erased from the line-set
  rw finset.ssubset_iff,
  use (line u v),
  split,
  {-- We show that `line u v` isn't in the line set by contradiction,
   -- showing that we may find a 3rd (forbidden) point on `line u v`.
   intro con,
   rw [line_set, finset.mem_image] at con,
   rcases con with ⟨pair, pair_def, eq⟩,
   rw finset.mem_filter at pair_def,
   have not_both_v : ↑(pair.1) ≠ v ∨ ↑(pair.2) ≠ v :=
    by {by_contra' K,
        apply pair_def.2,
        rw subtype.ext_iff,
        rw [K.1, K.2],
        },
   cases not_both_v,
   {apply uv_prop ↑(pair.1),
    {apply finset.erase_subset u P,
     exact pair.1.prop,},
    {apply @finset.ne_of_mem_erase _ _ P _ _,
     exact pair.1.prop,},
    {exact not_both_v,},
    {rw ←eq,
     apply left_mem_line,},
    },
   {apply uv_prop ↑(pair.2),
    {apply finset.erase_subset u P,
     exact pair.2.prop,},
    {apply @finset.ne_of_mem_erase _ _ P _ _,
     exact pair.2.prop,},
    {exact not_both_v,},
    {rw ←eq,
     apply right_mem_line,},
    },
   },
  -- Technicallities
  {intros l ldef,
   rw finset.mem_insert at ldef,
   cases ldef,
   {rw [ldef, line_set, finset.mem_image],
    use (⟨u,hu⟩,⟨v,hv⟩),
    split,
    {rw finset.mem_filter,
     split,
     apply finset.mem_univ,
     intro con,
     simp only [subtype.mk_eq_mk] at con,
     exact unv con,
     },
    {simp only [eq_self_iff_true, subtype.coe_mk],},
    },
   {rw [line_set, finset.mem_image] at *,
    rcases ldef with ⟨pair, pair_def, eq⟩,
    rw finset.mem_filter at pair_def,
    use ((⟨(pair.1.val), by {apply finset.erase_subset u P,
                              exact pair.1.prop,} ⟩ : ↥P),
          (⟨(pair.2.val), by {apply finset.erase_subset u P,
                              exact pair.2.prop,} ⟩ : ↥P)),
    split,
    {rw finset.mem_filter,
      split,
      apply finset.mem_univ,
      intro con,
      apply pair_def.2,
      rw subtype.ext_iff_val at *,
      simp only [subtype.val_eq_coe] at *,
      exact con,
      },
    {simp only [subtype.coe_mk, subtype.val_eq_coe],
      exact eq,},
    },
  },
end


/--
Attributed to Erdös and de Bruijn

If a finite set of points aren't aligned, then the number
of lines passing through pairs of these points is greater
then the number of points.
-/
theorem theorem_2
  (P : finset E) (hSG : ¬ (∃ a b : E, ∀ p ∈ P, p ∈ line a b)) :
  P.card ≤ (line_set P).card :=
begin
  revert hSG,
  -- We use strong induction
  apply finset.strong_induction_on P,
  intros S ih hSG_S,
  -- We consider `line u v` which contains no other points,
  -- which we obtain from Sylvester-Gallai.
  obtain ⟨u, uS, v, vS, uv_prop⟩ := Sylvester_Gallai S hSG_S,
  -- We disjoin cases on whether points are aligned if we deleter `u`
  set T := S.erase u with Tdef,
  by_cases aligned : ¬ (∃ a b : E, ∀ p ∈ T, p ∈ line a b),
  {-- If not, we may use the induction hypothesis on `P\u` and
   -- our lemma `list_set_lemma` to conclude
   specialize ih T 
      (by {apply finset.erase_ssubset,
           exact uS,})
      aligned,
   rw Tdef at ih,
   rw finset.card_erase_of_mem uS at ih,
   have bound := list_set_lemma S u v uS vS uv_prop.1 uv_prop.2,
   rw nat.lt_iff_add_one_le at bound,
   rw tsub_le_iff_right at ih,
   exact le_trans ih bound,
   },
  {-- Otherwise, the points are algined, say on `line a b`
   rw not_not at aligned,
   rcases aligned with ⟨a, b, ab_prop⟩,
   -- We consider the lines passing through `u`
   set L := finset.image (λ p : E, (line u p)) T with Ldef,
   -- The line all other points are on isn't part of it
   have : line a b ∉ L :=
    by {-- Otherwise, all points would be aligned
        by_contra K,
        apply hSG_S,
        use a,
        use b,
        intros p pS,
        by_cases Q : p ≠ u,
        {replace pS := finset.mem_erase.mpr ⟨Q,pS⟩,
         rw ← Tdef at pS,
         exact ab_prop p pS,
         },
        {rw not_ne_iff at Q,
         rw [Ldef, finset.mem_image] at K,
         rcases K with ⟨q, qdef, eq_lines⟩,
         rw [←eq_lines,Q],
         apply left_mem_line,
         },
        },
   -- The number of lines of the "pencil" lower-bounds the
   -- number of lines of the line set
   have that : (insert (line a b) L).card ≤ (line_set S).card :=
    by {-- This due to them being a subset of the line set
        apply finset.card_le_of_subset,
        intros l ldef,
        rw finset.mem_insert at ldef,
        rw [line_set, finset.mem_image],
        cases ldef,
        {-- For `line a b` we need two points of `P` that represent it
         have Tsize : 2 ≤ T.card :=
          by {apply_fun finset.card at Tdef,
              nth_rewrite_rhs 0 finset.card_erase_of_mem uS at Tdef,
              linarith [Sylvester_Gallai_condition_fact S hSG_S,
                        (show 1 ≤ S.card, by {rw ←zero_add 1,
                                              rw ←nat.lt_iff_add_one_le,
                                              rw finset.card_pos,
                                              use u,
                                              exact uS,} )],},
          obtain ⟨x,y,xdef,ydef,xny⟩ := pair_of_2_le_card Tsize,
          rw [Tdef] at xdef ydef,
          use (⟨x,(finset.erase_subset u S) xdef⟩, ⟨y,((finset.erase_subset u S) ydef)⟩),
          split,
          {simp only [true_and, finset.mem_univ, subtype.mk_eq_mk, finset.mem_filter],
           apply subtype.ne_of_val_ne,
           simp only [ne.def],
           exact xny,},
          {simp only [subtype.coe_mk],
           rw [← Tdef] at xdef ydef,
           rw ← line_rw_of_mem_of_mem xny
            (ab_prop x xdef)
            (ab_prop y ydef),
            exact ldef.symm,
            },
        },
        {-- For th others, we just need a lot of rewriting
         rw [Ldef, finset.mem_image] at ldef,
         rcases ldef with ⟨t,tdef,teq⟩,
         rw Tdef at tdef,
         use (⟨u,uS⟩, ⟨t,((finset.erase_subset u S) tdef)⟩),
         split,
         {rw finset.mem_filter,
          split,
          apply finset.mem_univ,
          simp only [subtype.mk_eq_mk, ne.def],
          intro con,
          apply finset.not_mem_erase u S,
          nth_rewrite 0 con,
          exact tdef,
          },
          {simp only [subtype.coe_mk],
           exact teq,},
        },
      },
   -- There are as many lines at the tip of the "pencil" as there
   -- are points alinged on `line a b`.
   have thut : T.card = L.card :=
    by {-- We let points and lines correspond
        apply finset.card_congr (λ t, λ tdef : t ∈ T, line u t),
        -- Mappping condition
        {intros t tdef,
         dsimp,
         rw Ldef,
         rw finset.mem_image,
         use t,
         split,
         exact tdef,
         refl,},
        -- Injectivity
        {intros s t sdef tdef st_eq,
         dsimp at st_eq,
         by_contra K,
         have problem_1 :=
          line_rw_of_mem_of_mem K
           (ab_prop s sdef)
           (ab_prop t tdef),
         have problem_2 : line u t = line s t :=
          by {apply  line_rw_of_mem_of_mem K,
              rw ← st_eq,
              apply right_mem_line,
              apply right_mem_line,
              },
        apply hSG_S,
        use a, use b,
        intros p pS,
        by_cases Q : p ≠ u,
        {replace pS := finset.mem_erase.mpr ⟨Q,pS⟩,
         rw ← Tdef at pS,
         exact ab_prop p pS,
         },
        {rw not_ne_iff at Q,
         rw [Q, problem_1, ←problem_2],
         apply left_mem_line,
         },
        },
        -- Surjectivity
        {intros l ldef,
         rw [Ldef, finset.mem_image] at ldef,
         rcases ldef with ⟨t, tdef , teq⟩,
         use t,
         split,
         {dsimp,
          exact teq,},
         {exact tdef,},
        }
        },
   -- Form here, we do some accounting
   apply_fun finset.card at Tdef,
   nth_rewrite_rhs 0 finset.card_erase_of_mem uS at Tdef,
   rw finset.card_insert_of_not_mem this at that,
   rw [← thut, Tdef] at that,
   rw nat.sub_add_cancel at that,
   {exact that,},
   {rw ← zero_add 1,
    rw ←nat.lt_iff_add_one_le,
    rw finset.card_pos,
    use u,
    exact uS,
    },
   },
end


open finset

open_locale classical

-- An alias/shortcut I'd like to see in mathlib
lemma fintype.univ_filter_eq_card_iff
  {α : Type} [fintype α] {p : α → Prop } [decidable_pred p]:
  ((univ.filter p).card = fintype.card α ) ↔ (∀ x : α, p x) :=
begin
  --library_search, --fails
  rw card_eq_iff_eq_univ,
  rw filter_eq_self,
  simp?,
end

/--
In the context of `theorem_3`, we must have `r x < m`,
for it ca be at most `m` and assuming equility is contradictory.
-/
lemma theorem_3_ub
  {α : Type} [decidable_eq α]
  {X : finset α} (hX : 3 ≤ X.card)
  {m : ℕ}
  {A : fin m → finset α} (hA : ∀ i : fin m, A i ⊂ X)
  (h : ∀ x y, x ∈ X → y ∈ X → x ≠ y →
        (∃ i, x ∈ A i ∧ y ∈ A i ∧ (∀ j, (x ∈ A j ∧ y ∈ A j) → j = i)))
  (r : Π (x : α), x ∈ X → ℕ )
  (rdef : r = λ (x : α) (xX : x ∈ X), (filter (λ (i : fin m), x ∈ A i) univ).card)
  (hr : ∃ x, ∃ h : x ∈ X, r x h = m ) :
  false :=
begin
  -- This proof is best understood by consulting the figure
  -- in our thesis
  rcases hr with ⟨y,yX,rym⟩, 
  rw rdef at rym,
  dsimp at rym,
  --rw (fintype.card_fin m) at rym, --fails... 
  replace rym := eq.trans rym (fintype.card_fin m).symm,
  rw fintype.univ_filter_eq_card_iff at rym,
  obtain ⟨a,adef⟩ :=
      card_pos.mp
      (show 0 < (X.erase y).card,
        by {rw card_erase_of_mem yX,
            linarith [(show 1 ≤ X.card, by {linarith,})],}),
  set Aay := classical.some (h a y ((erase_subset y X) adef) yX (ne_of_mem_erase adef)) with Aay_def,
  have Aay_prop := classical.some_spec (h a y ((erase_subset y X) adef) yX (ne_of_mem_erase adef)),
  rw ← Aay_def at Aay_prop, 
  obtain ⟨b,bdef,bprop⟩ := (ssubset_iff_of_subset (subset_of_ssubset (hA Aay))).mp (hA Aay),
  have bny : b ≠ y :=
    by {intro con,
        rw con at bprop,
        exact bprop Aay_prop.2.1,
        },
  set Aby := classical.some (h b y bdef yX bny) with Aby_def,
  have Aby_prop := classical.some_spec (h b y bdef yX bny),
  rw ← Aby_def at Aby_prop,
  have anb : a ≠ b :=
    by {intro con,
        rw ←con  at bprop,
        exact bprop Aay_prop.1,
        },
  set Aab := classical.some (h a b ((erase_subset y X) adef) bdef anb) with Aab_def,
  have Aab_prop := classical.some_spec (h a b ((erase_subset y X) adef) bdef anb),
  rw ← Aab_def at Aab_prop, 
  have eq1 := Aay_prop.2.2 Aab ⟨Aab_prop.1, rym Aab⟩,
  have eq2 := Aby_prop.2.2 Aab ⟨Aab_prop.2.1, rym Aab⟩, 
  apply bprop,
  rw [← eq1, eq2],
  exact Aby_prop.1,  
end


/--
We show the bound `|Aᵢ| ≤ r x for x ∉ Aᵢ` from `theorem_3`. 
-/
lemma theorem_3_lb
  {α : Type} [decidable_eq α]
  {X : finset α} (hX : 3 ≤ X.card)
  {m : ℕ}
  {A : fin m → finset α} (hA : ∀ i : fin m, A i ⊂ X)
  (h : ∀ x y, x ∈ X → y ∈ X → x ≠ y →
        (∃ i, x ∈ A i ∧ y ∈ A i ∧ (∀ j, (x ∈ A j ∧ y ∈ A j) → j = i)))
  (r : Π (x : α), x ∈ X → ℕ )
  (rdef : r = λ (x : α) (xX : x ∈ X), (filter (λ (i : fin m), x ∈ A i) univ).card):
  ∀ x ∈ X, ∀ i, x ∉ A i → (A i).card ≤ r x (by {assumption}) :=
begin
  intros x xX j xnA,
  rw rdef,
  -- We associate to each element of Aⱼ one of the Aₖ
  -- that contains the element and x 
  set f := (λ y, λ hy : y ∈ (A j), 
                (classical.some (h x y xX --((subset_of_ssubset (hA j)) hy) --fails
                    (by {apply (subset_of_ssubset (hA j)),
                        exact hy,})
                    (by {intro con,
                        apply xnA,
                        rw con,
                        exact hy,}))))
            with fdef,
  -- We use the set of these Aₖ to make the comparison
  set I := image (λ z : (A j), f z.val z.prop) (A j).attach with Idef,
  apply @le_of_eq_of_le _ _ _ I.card _,
  {-- We show that the correspondence is a bijection
   apply card_congr f,
   -- map
   {intros a ha,
    rw Idef,
    rw mem_image,
    use ⟨a,ha⟩,
    split,
    apply mem_attach,
    dsimp,
    refl,
    },
   -- Injectivity
   {intros a b adef bdef eq,
    simp only [fdef] at eq,
    -- We introduc noatation and defining properties:
    set ca := (classical.some (h x a xX 
                    (by {apply (subset_of_ssubset (hA j)),
                         exact adef,})
                    (by {intro con,
                         apply xnA,
                         rw con,
                         exact adef,}))) with cadef,
    have Ca := (classical.some_spec (h x a xX 
                    (by {apply (subset_of_ssubset (hA j)),
                         exact adef,})
                    (by {intro con,
                         apply xnA,
                         rw con,
                         exact adef,}))),
    set cb := (classical.some (h x b xX 
                    (by {apply (subset_of_ssubset (hA j)),
                         exact bdef,})
                    (by {intro con,
                         apply xnA,
                         rw con,
                         exact bdef,}))) with cbdef,        
    have Cb := (classical.some_spec (h x b xX 
                    (by {apply (subset_of_ssubset (hA j)),
                         exact bdef,})
                    (by {intro con,
                         apply xnA,
                         rw con,
                         exact bdef,}))),
    -- If `a ≠ b`, we would get on more Aₖ containg this pair,
    -- which by uniquness of of the sets containing a given pair
    -- must be Aⱼ
    by_contra con,
    set cab := (classical.some (h a b
                    (by {apply (subset_of_ssubset (hA j)),
                         exact adef,})
                    (by {apply (subset_of_ssubset (hA j)),
                         exact bdef,})
                    (con))) with cabdef,
    have Cab := (classical.some_spec (h a b
                    (by {apply (subset_of_ssubset (hA j)),
                         exact adef,})
                    (by {apply (subset_of_ssubset (hA j)),
                         exact bdef,})
                    (con))),
    rw [← cadef] at *,
    rw [← cbdef] at *,
    rw [← cabdef] at *,
    -- By the injectity assumption `eq` and uniqness of the sets
    -- containing a given pair, A ca and A cb are the same set,
    -- wich contains x and the pair a b, so that these sets must
    -- coinicide with A j, whcih contradicts x ∉ A j. 
    apply xnA,
    rw eq at Ca,
    rw (Cab.2.2 j ⟨adef,bdef⟩),
    rw ← (Cab.2.2 cb ⟨Ca.2.1,Cb.2.1⟩),
    exact Cb.1,
    },
   -- Surjectivity
   {intros b bI,
    rw [Idef, mem_image] at bI,
    rcases bI with ⟨c,cdef,ceq⟩,
    use c.val, use c.prop,
    exact ceq,},
   },
  {-- We obtain this bound from the sets being subsets,
   -- as all sets of I contain x by definition
   dsimp,
   apply card_le_of_subset,
   rw Idef,
   intros i idef,
   rw mem_filter,
   split,
   apply mem_univ,
   rw mem_image at idef,
   rcases idef with ⟨c,cdef,ceq⟩,
   rw fdef at ceq,
   dsimp at ceq,
   rw ← ceq,
   exact (classical.some_spec (h x ↑c xX
              (by {apply (subset_of_ssubset (hA j)),
                   exact c.prop,})
              (by {intro con,
                   apply xnA,
                   rw con,
                   exact c.prop,}))).1,
   },
end



open_locale big_operators

/-- An algeraic rewrite-/
lemma splitter
  {α : Type} [decidable_eq α] (X : finset α) (hX : 0 < X.card) :
  (1 : ℚ) = ∑ x in X, (1/X.card : ℚ) :=
begin
  have : (X.card : ℚ) ≠ 0 :=
    by {intro con,
        rw nat.cast_eq_zero at con,
        rw con at hX,
        exact (lt_irrefl 0) hX,
        },
  nth_rewrite 0 ← mul_one_div_cancel this,
  nth_rewrite 0 (card_eq_sum_ones X),
  push_cast,
  rw [zero_add],
  --rw @sum_div _ _ _ X (λ y, (1 : ℚ)) (X.card : ℚ), --fails
  simp only [one_div, mul_eq_mul_left_iff, finset.sum_const, finset.card_eq_zero,
             nsmul_eq_mul, true_or, eq_self_iff_true, nat.cast_inj, inv_inj,
             nat.cast_eq_zero, finset.sum_congr, nat.smul_one_eq_coe],
end

-- An alias/shortcut I'd like to see in mathlib
lemma sum_rel
  {α β : Type} [decidable_eq α] [decidable_eq β]
  (X : finset α) (U : finset β)
  (r : α → β → Prop)
  {hr : ∀ x : α, ∀ y : β, decidable (r x y) }
  (f : α → β → ℚ) :
  ∑ x in X, (∑ i in (U.filter (λ i, r x i)), f x i) =
  ∑ i in U, (∑ x in (X.filter (λ x, r x i)), f x i) :=
begin
  simp_rw sum_filter,
  rw sum_comm,
end


/--
Attributed to Motzkin or Conway

Generalises `theorem_2` to more abstract incidence geometries.
-/
theorem theorem_3
  {α : Type} [decidable_eq α]
  (X : finset α) (hX : 3 ≤ X.card)
  (m : ℕ) (hm : 0 < m)
  (A : fin m → finset α) (hA : ∀ i : fin m, A i ⊂ X)
  (h : ∀ x y, x ∈ X → y ∈ X → x ≠ y →
        (∃ i, x ∈ A i ∧ y ∈ A i ∧ (∀ j, (x ∈ A j ∧ y ∈ A j) → j = i))):
  X.card ≤ m :=
begin
  -- We deinie the number of appearance of an x in the sets Aᵢ
  set r := (λ x : α, λ xX : x ∈ X, (univ.filter (λ i, x ∈ A i)).card)
    with rdef,
  -- We derive r x < m
  by_cases Q : ∃ x, ∃ h : x ∈ X, r x h = m,
  {exfalso,
   apply theorem_3_ub hX hA h r rdef Q,
   },
  {push_neg at Q,
   -- We have r x ≤ m via subsets, so that in our case:
   replace Q : ∀ (x : α) (h : x ∈ X), r x h < m :=
      by {intros x xdef,
          apply lt_of_le_of_ne _ (Q x xdef),
          rw rdef,
          dsimp,
          --rw ← (fintype.card_fin m), --fails
          convert (card_filter_le univ (λ (i : fin m), x ∈ A i)),
          rw card_univ,
          rw fintype.card_fin m,
          },
   -- we recall our previously derived bound
   have lb := theorem_3_lb hX hA h r rdef,
   by_contra' con,
   -- We set up the main bound that will yield a contradiction
   -- from some algebraic manipulations
   have bound : ∀ x ∈ X, ∀ i, x ∉ A i →
      (1/(m * (X.card - (A i).card)) : ℚ)
      < (1/(X.card * (m - r x (by {assumption}))) : ℚ) :=
      by {intros x hx i xnA,
          apply div_lt_div' (le_refl (1 : ℚ)) _ (by {norm_num}),
          {apply mul_pos,
           rw nat.cast_pos,
           exact lt_trans hm con,
           rw sub_pos,
           rw nat.cast_lt,
           exact Q x hx,
           },
          {rw [mul_sub,mul_sub],
           rw mul_comm,
           rw sub_lt_sub_iff_left,
           apply mul_lt_mul_of_nonneg_of_pos,
           {rw nat.cast_lt,
           exact con},
           {rw nat.cast_le,
            apply lb x hx i xnA,},
           {apply nat.cast_nonneg,},
           {rw nat.cast_pos,
            simp only [rdef],
            rw card_pos,
            obtain ⟨a,adef⟩ :=
              card_pos.mp
              (show 0 < (X.erase x).card,
                by {rw card_erase_of_mem hx,
                    linarith [(show 1 ≤ X.card, by {linarith,})],}),
            use (classical.some (h a x ((erase_subset x X) adef) hx (ne_of_mem_erase adef))),
            rw mem_filter,
            split,
            apply mem_univ,
            exact (classical.some_spec (h a x ((erase_subset x X) adef) hx (ne_of_mem_erase adef))).2.1,
            },
           },
          },
  -- We contradiciton will stem from 1<1, via so rewrites and `bound`
  apply lt_irrefl (1 : ℚ),
  nth_rewrite 1 splitter X (by {linarith,}),
  nth_rewrite 0 splitter (univ : finset (fin m)) (by {rw [card_univ, fintype.card_fin], exact hm,}),
  have rw_left :
    ∑ x in X, (1/X.card : ℚ) =
    ∑ x in X.attach, (∑ i in (univ.filter (λ i, ↑x ∉ A i)), (1/(X.card * (m - r ↑x x.prop)) : ℚ)) :=
      -- Note: we need an `attach` to define r
      by {rw ← sum_attach,
          apply sum_congr,
          refl,
          intros x xX,
          rw ← one_div_mul_one_div,
          rw ←mul_sum,
          nth_rewrite 0 ← (mul_one (1/X.card : ℚ)),
          rw mul_eq_mul_left_iff,
          left,
          have : 0 < (univ.filter (λ i, ↑x ∉ A i)).card :=
            by {rw card_pos,
                by_contra' K,
                rw [finset.nonempty] at K,
                push_neg at K,
                apply theorem_3_ub hX hA h r rdef,
                use ↑x, use x.prop,
                rw rdef,
                dsimp,
                --rw ← (fintype.card_fin m), --fails
                have : (univ.filter (λ i, ↑x ∈ A i)) = univ :=
                  by {rw filter_eq_self,
                      intros y yu,
                      by_contra' ycon,
                      apply K y,
                      rw mem_filter,
                      split,
                      exact yu,
                      exact ycon,
                      },
                rw this,
                rw [card_univ, fintype.card_fin],
                },
          nth_rewrite 0 splitter (univ.filter (λ i, ↑x ∉ A i)) this,
          clear this,
          have : (univ.filter (λ i, ↑x ∉ A i)).card = m - (r ↑x x.prop) :=
            by {rw ← compl_filter,
                rw card_compl,
                rw [rdef, fintype.card_fin],
                }, 
          rw this,
          rw nat.cast_sub,
          exact le_of_lt (Q ↑x x.prop),
          },
  rw rw_left,
  clear rw_left,
  have rw_right :
    ∑ (i : fin m), 1 / ((univ : finset (fin m)).card : ℚ) =
    ∑ (i : fin m), (∑ x in (X.attach.filter (λ x, ↑x ∉ A i)), (1/(m * (X.card - (A i).card)) : ℚ)) :=
      by {apply sum_congr,
          refl,
          intros i iu,
          rw ← one_div_mul_one_div,
          rw ←mul_sum,
          nth_rewrite 0 ← (mul_one (1/univ.card : ℚ)),
          rw [card_univ, fintype.card_fin],
          rw mul_eq_mul_left_iff,
          left,
          have : 0 < ((X.attach.filter (λ x, ↑x ∉ A i))).card :=
            by {rw card_pos,
                obtain ⟨y,ynA,ymem⟩ := ssubset_iff.mp (hA i),
                use ⟨y, ymem (mem_insert_self y (A i))⟩,
                rw mem_filter,
                split,
                apply mem_attach,
                simp only [subtype.coe_mk],
                exact ynA,
                },
          nth_rewrite 0 splitter ((X.attach.filter (λ x, ↑x ∉ A i))) this,
          clear this,
          have : (X.attach.filter (λ x, ↑x ∉ A i)).card = X.card - (A i).card :=
            by {rw filter_not,
                rw ← (card_sdiff (subset_of_ssubset (hA i))),
                nth_rewrite 0 ← (show (X ∩ A i) = A i,
                      by {rw inter_eq_right_iff_subset,
                          exact subset_of_ssubset (hA i),
                          }),
                rw ← filter_mem_eq_inter,
                rw eq_comm,
                apply card_congr
                  (λ x, λ hx : x ∈ (X \ filter (λ (j : α), j ∈ A i) X),
                    (⟨x, (sdiff_subset X (filter (λ (j : α), j ∈ A i) X)) hx⟩
                      : {x // x∈X})),
                -- map
                {intros a adef,
                 dsimp,
                 rw mem_sdiff,
                 split,
                 apply mem_attach,
                 intro K,
                 rw mem_filter at K,
                 rw mem_sdiff at adef,
                 apply adef.2,
                 rw mem_filter,
                 rw subtype.coe_mk at K,
                 exact ⟨adef.1,K.2⟩,
                 },
                -- inj
                {intros a b adef bdef eq,
                 dsimp at eq,
                 rw subtype.mk_eq_mk at eq,
                 exact eq,},
                -- surj
                {intros b bdef,
                 use ↑b,
                 have : ↑b ∈ X \ filter (λ (j : α), j ∈ A i) X :=
                   by {rw mem_sdiff,
                       rw mem_sdiff at bdef,
                       split,
                       exact b.prop,
                       rw mem_filter,
                       rw mem_filter at bdef,
                       intro K,
                       apply bdef.2,
                       exact ⟨mem_attach X b, K.2⟩,
                       },
                 use this,
                 simp only [eq_self_iff_true, finset.mk_coe],
                 }
                }, 
          rw this,
          rw nat.cast_sub,
          exact card_le_of_subset (subset_of_ssubset (hA i)),
          }, 
  rw rw_right,
  clear rw_right,
  -- To make the comparison, we first swap sums:
  have := sum_rel X.attach (univ : finset (fin m)) (λ x, λ i, ↑x ∉ A i) (λ x, λ i, (1/(X.card * (m - r ↑x x.prop)) : ℚ)),
  dsimp at this,
  rw this,
  -- Then we compare sums, which due to < requires showing
  -- non-emptyness of index sets
  apply sum_lt_sum_of_nonempty,
  {exact @univ_nonempty _ _ (fin.pos_iff_nonempty.mp hm),},
  intros i idef,
  apply sum_lt_sum_of_nonempty,
  {obtain ⟨y,ynA,ymem⟩ := ssubset_iff.mp (hA i),
   use y,
   exact ymem (mem_insert_self y (A i)),
   rw mem_filter,
   split,
   apply mem_attach,
   exact ynA,
   },
  -- In this second comparision, we make use of `bound`
   intros x xdef,
   rw mem_filter at xdef,
   exact bound ↑x x.prop i xdef.2, 
  },
end


open simple_graph

/--
If we decompose a complete graph Kₙ into m cliques different
from  Kₙ, such that every edge is in a unique clique, then m ≥ n.

This is a first verison, with a direct definition of cliques
-/
lemma clique_decomposition
  {V : Type} [fintype V] [decidable_eq V] {m : ℕ}
  (hV : 3 ≤ fintype.card V) (hm : 0 < m)
  (D : fin m → subgraph (complete_graph V))
  (hD_1 : ∀ i : fin m, (D i).verts.to_finset ⊂ (univ : finset V))
  --(hD_2 : ∀ i : fin m, (subgraph.coe (D i)) = complete_graph ↥(D i).verts) -- bad (?) formalisation
  (hD_2 : ∀ i : fin m, (subgraph.spanning_coe (D i)).adj =
                          (λ x y, if (x ∉ (D i).verts ∨ y ∉ (D i).verts)
                                  then false
                                  else x ≠ y))
  (h : ∀ e, e ∈ (complete_graph V).edge_finset →
        (∃ i, (e ∈ edge_finset (subgraph.spanning_coe (D i)))
            ∧ (∀ j, e ∈ edge_finset (subgraph.spanning_coe (D j)) → j = i ))):
  fintype.card V ≤ m :=
begin
  rw ← card_univ,
  rw ← card_univ at hV,
  -- We apply `theorem_3` on the vertices,
  -- where Aᵢ is the vertex set of clique i
  set A := (λ i : fin m, (D i).verts.to_finset) with Adef,
  replace hD_1 : ∀ i, A i ⊂ univ :=
    by {intro i,
        simp only [Adef],
        exact hD_1 i,} ,
  apply theorem_3 (univ : finset V) hV m hm A hD_1,
  intros x y xu yu xny,
  specialize h ⟦(x,y)⟧ _,
  {rw [mem_edge_finset, mem_edge_set],
   dsimp [complete_graph],
   exact xny,
   },
  rcases h with ⟨i,i_prop,i_uni⟩,
  use i,
  split,
  {rw [mem_edge_finset, mem_edge_set] at i_prop,
   replace i_prop := (D i).edge_vert i_prop,
   simp only [Adef],
   rw set.mem_to_finset,
   exact i_prop,
   },
  split,
  {rw [mem_edge_finset, mem_edge_set] at i_prop,
   replace i_prop := (D i).edge_vert (adj.symm i_prop),
   simp only [Adef],
   rw set.mem_to_finset,
   exact i_prop,
   },
  {intros j j_prop,
   apply i_uni j,
   rw [mem_edge_finset, mem_edge_set],
   simp only [Adef, set.mem_to_finset] at j_prop,
   simp only [hD_2 j],
   rw if_neg _,
   exact xny,
   push_neg,
   exact j_prop,
  },
end


/--
If we decompose a complete graph Kₙ into m cliques different
from  Kₙ, such that every edge is in a unique clique, then m ≥ n.

This is a second verison, with a mathlibs notion of cliques
-/
lemma clique_decomposition'
  {V : Type} [fintype V] [decidable_eq V] {m : ℕ}
  (hV : 3 ≤ fintype.card V) (hm : 0 < m)
  (D : fin m → subgraph (complete_graph V))
  (hD_1 : ∀ i : fin m, (D i).verts.to_finset ⊂ (univ : finset V))
  (hD_2 : ∀ i : fin m, is_clique (subgraph.spanning_coe (D i)) (D i).verts)
  (h : ∀ e, e ∈ (complete_graph V).edge_finset →
        (∃ i, (e ∈ edge_finset (subgraph.spanning_coe (D i)))
            ∧ (∀ j, e ∈ edge_finset (subgraph.spanning_coe (D j)) → j = i ))):
  fintype.card V ≤ m :=
begin
  rw ← card_univ,
  rw ← card_univ at hV,
  set A := (λ i : fin m, (D i).verts.to_finset) with Adef,
  replace hD_1 : ∀ i, A i ⊂ univ :=
    by {intro i,
        simp only [Adef],
        exact hD_1 i,} ,
  apply theorem_3 (univ : finset V) hV m hm A hD_1,
  intros x y xu yu xny,
  specialize h ⟦(x,y)⟧ _,
  {rw [mem_edge_finset, mem_edge_set],
   dsimp [complete_graph],
   exact xny,
   },
  rcases h with ⟨i,i_prop,i_uni⟩,
  use i,
  split,
  {rw [mem_edge_finset, mem_edge_set] at i_prop,
   replace i_prop := (D i).edge_vert i_prop,
   simp only [Adef],
   rw set.mem_to_finset,
   exact i_prop,
   },
  split,
  {rw [mem_edge_finset, mem_edge_set] at i_prop,
   replace i_prop := (D i).edge_vert (adj.symm i_prop),
   simp only [Adef],
   rw set.mem_to_finset,
   exact i_prop,
   },
  -- merely this code block differes from the previous proof
  {intros j j_prop,
   apply i_uni j,
   rw [mem_edge_finset, mem_edge_set],
   simp only [Adef, set.mem_to_finset] at j_prop,
   specialize hD_2 j,
   rw is_clique_iff at hD_2,
   specialize hD_2 j_prop.1 j_prop.2 xny,
   exact hD_2,
  },
end

#check simple_graph.embedding

