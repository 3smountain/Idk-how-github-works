Unset Universe Checking.
Require Export UniMath.Foundations.All.
Require Export UniMath.MoreFoundations.All.

(* You can use any result from previous homeworks, exercises, or lectures without proof.*)

(* Exercise 1 *)

(* Define the type of groups. *)

Definition Grp := ∑ G : Set, ∑ e:G, ∑ m: G→ G→ G, ∑ i:G→ G, (∏ g:G, ((m e g)=g)×((m g e)=g)×((m g (i g))=e)× ((m(i g)g)=e))×(∏ h g l:G, (m (m h g) l)=(m h (m g l))).

(* Exercise 2 *)

(* Give a group structure on the booleans ~bool~ and show that it produces a term of the type of groups. Use the fact ~isasetbool~ that ~bool~ is a set.*)

Definition boolmult: bool→ bool→ bool.
Proof.
intro b.
intro c.
induction b.
  - induction c.
    +exact true.
    +exact false.
  - induction c.
    +exact false.
    +exact true.
Defined.

Theorem boolisgroup: Grp.
Proof.
    unfold Grp.
    use tpair.
    - exact bool.
    - use tpair.
      + exact true.
      + use tpair.
        -- exact boolmult.
        -- use tpair.
           --- exact (idfun bool).
           --- split.
               * intro g.
                 split.
                 ** induction g.
                    *** cbn.
                        apply idpath.
                    *** cbn.
                        apply idpath.
                 ** split.
                    ---- induction g.
                         *** cbn.
                             apply idpath.
                         *** cbn.
                             apply idpath.
                    ---- split.
                         **** induction g.
                              *** cbn.
                                  apply idpath.
                              *** cbn.
                                  apply idpath.
                         **** induction g.
                              *** cbn.
                                  apply idpath.
                              *** cbn.
                                  apply idpath.
             * intros h g l.
               induction h.
               ** induction g.
                  ---- induction l.
                       *** cbn.
                           apply idpath.
                       *** cbn.
                           apply idpath.
                  ---- induction l.
                       *** cbn.
                           apply idpath.
                       *** cbn.
                           apply idpath.
              ** induction g.
                  ---- induction l.
                       *** cbn.
                           apply idpath.
                       *** cbn.
                           apply idpath.
                  ---- induction l.
                       *** cbn.
                           apply idpath.
                       *** cbn.
                           apply idpath.
                    
Defined.


(* Exercise 3 *)

(* Formalize a (simple) fact or construction about groups that you like. E.g., the fact that inverses are unique, or the definition of subgroup. *)
Theorem left_inverses_unique {G : Grp} {l g: pr1 G}: (pr1 (pr2 (pr2 G)))  l g=pr1 (pr2 G)→ l=(pr1 (pr2 (pr2 (pr2 G)))) g.
Proof. 
    induction G as [H t1].
    induction t1 as [e t2].
    induction t2 as [m t3].
    induction t3 as [i c].
    induction c as [d f].
    cbn.
    set (d1:=d l).
    set (k1:=d g).
    induction d1 as [d2 d3].
    induction d3 as [d4 d5].
    induction d5 as [d6 d7].
    induction k1 as [k2 k3].
    induction k3 as [k4 k5].
    induction k5 as [k6 k7].
    intro p.
    rewrite (pathsinv0 d4).
    rewrite (pathsinv0 k6).
    rewrite (pathsinv0 (f l g (i g))).
    rewrite p.
    apply d.
Defined.

Theorem right_inverses_unique {G : Grp} {h g: pr1 G}: (pr1 (pr2 (pr2 G)))  g h=pr1 (pr2 G)→ h=(pr1 (pr2 (pr2 (pr2 G)))) g.
Proof. 
    induction G as [H t1].
    induction t1 as [e t2].
    induction t2 as [m t3].
    induction t3 as [i c].
    induction c as [d f].
    cbn.
    set (d1:=d h).
    set (k1:=d g).
    induction d1 as [d2 d3].
    induction d3 as [d4 d5].
    induction d5 as [d6 d7].
    induction k1 as [k2 k3].
    induction k3 as [k4 k5].
    induction k5 as [k6 k7].
    intro p.
    rewrite (pathsinv0 d2).
    rewrite (pathsinv0 k7).
    rewrite (f (i g) g h).
    rewrite p.
    apply d.
Defined.

Theorem left_inverse_is_right_inverse {G : Grp} {h g l: pr1 G}: (pr1 (pr2 (pr2 G)))  g h=pr1 (pr2 G)→ (pr1 (pr2 (pr2 G)))  l g =pr1 (pr2 G)→ h=l.
Proof.
  intro t.
  intro r.
  set (t1:= right_inverses_unique t).
  rewrite t1.
  set (r1:= left_inverses_unique r).
  rewrite r1.
  apply idpath.
Defined.

(* Exercise 4 *)

(* Define the universe of pointed types as follows. *)

Definition PtdUU := ∑ T : UU, T.

(* Formulate a notion of equivalence between pointed types and show that such an equivalence induces an identity between pointed types (not only of the carriers).
   You may want to use the following lemmas from the libray: `total2_paths2_f`, `weqtopaths`, `weqpath_transport`. *)

(*
Print weq.
Print weqtopaths.
Print weqpath_transport.
Print total2_paths2_f.
*)

Definition Pweq:= λ P Q: PtdUU, ∑ f : (pr1 P)≃(pr1 Q), (f (pr2 P)= (pr2 Q)).

Theorem Pweq_to_id (P Q: PtdUU): (Pweq P Q)→ P=Q.
Proof.
    intro f1.
    unfold Pweq in f1.
    induction P as [P1 p].
    induction Q as [Q1 q].
    induction f1 as [f h].
    cbn in f.
    cbn in h.
    use total2_paths2_f.
    - apply weqtopaths.
      exact f.
    - rewrite weqpath_transport.
      apply h.
Defined.
    

(* Exercise 5 *)

(* Show univalence for the universe of pointed types, i.e. that the function defined in Exercise 4 induces an equivalence. *)
(* Note: This is quite harder than all previous exercises! You can use any lemma defined in the imported files *)

(*
Search weqtopaths.

Print eqweqmap_weqtopaths.
Print eqweqmap.
Print weqpath_cast.
Print cast.
*)

(* Eventually we want to use twooutof3a. So we are building to that*)

Print total2_paths2_f.

Definition sepid:=λ P Q: PtdUU, (∑ e : (pr1 P)=(pr1 Q), (transportf (λ T : UU, T) e) (pr2 P)= (pr2 Q)).

Theorem id_to_sepid (P Q:PtdUU): P=Q→ (sepid P Q).
Proof.
  intro t.
  use tpair.
  - induction t.
    apply idpath.
  - induction t.
    cbn.
    apply idpath.
Defined.

Theorem sepid_to_id (P Q:PtdUU): (sepid P Q)→ P=Q.
Proof.
  intro t.
  induction t as [e h].
  induction P as [P1 p].
  induction Q as [Q1 q].
  use total2_paths2_f.
  - exact e.
  - cbn in e.
    cbn in h.
    exact h.
Defined.

Theorem sepid_to_id_is_equiv {P Q:PtdUU}: isweq (sepid_to_id P Q).
Proof.
  use isweq_iso.
  - exact (id_to_sepid P Q).
  - intro x.
    induction P as [P1 p].
    induction Q as [Q1 q].
    induction x as [e h].
    cbn in e.
    cbn in h.
    induction e.
    induction h.
    cbn.
    use total2_paths2_f.
    + cbn.
      apply idpath.
    + cbn.
      apply idpath.
  - intro y.
    induction y.
    cbn.
    induction P as [P1 p].
    apply idpath.
Defined.

Theorem sepid_to_Pweq (P Q:PtdUU): (sepid P Q)→ (Pweq P Q).
Proof.
  intro x.
  induction x as [e h].
  induction P as [P1 p].
  induction Q as [Q1 q].
  cbn in e.
  use tpair.
  - cbn.
    apply (eqweqmap e).
  - cbn.
    cbn in h.
    induction e.
    cbn in h.
    cbn.
    apply h.
Defined.

Theorem Pweq_to_sepid (P Q:PtdUU): (Pweq P Q) → (sepid P Q).
Proof.
  intro f1.
  induction f1 as [f e].
  use tpair.
  - use weqtopaths.
    exact f.
  - cbn.
    rewrite weqpath_transport.
    exact e.
Defined.

Theorem Pweq_to_sepid_is_equiv {P Q:PtdUU}: isweq (Pweq_to_sepid P Q).
Proof.
  use isweq_iso.
  - exact (sepid_to_Pweq P Q).
  - intro x.
    induction x as [f h].
    induction P as [P1 p].
    induction Q as [Q1 q].
    simpl in *.
    use total2_paths2_f.
    + cbn.
      apply eqweqmap_weqtopaths.
    + cbn.
      induction h.
      cbn.
      
      (* want to use rewrite weqpath_transport but unimath refuses*)
Admitted.

Theorem commutativediagram_c {P Q:PtdUU}: (Pweq_to_id P Q)=(sepid_to_id P Q) ∘ (Pweq_to_sepid P Q).
Proof.
  use funextsec.
  intro f.
  induction f as [f1 c].
  cbn.
  unfold Pweq_to_id.
  unfold sepid_to_id.
  unfold Pweq_to_sepid.
  cbn.
  apply idpath.
Defined.  

Theorem Pweqtoid_is_equiv {P Q: PtdUU}: isweq (Pweq_to_id P Q).
Proof.
  rewrite commutativediagram_c.
  use twooutof3c.
  - exact Pweq_to_sepid_is_equiv.
  - exact sepid_to_id_is_equiv.
Defined.
      
