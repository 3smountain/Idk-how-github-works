Unset Universe Checking.
Require Export UniMath.Foundations.All.
Require Export UniMath.CategoryTheory.All.

(* Instructions: do Exercises 1, 2 and 3 here in UniMath. Do Exercise 4 in LaTeX. No exercise should be done both in UniMath and LaTeX. As usual, you will submit one .v file and one .pdf file.*)

(* You can use anything proven in previous exercises or homework, and
`impred_isaprop`, `funextsec`, `weqtopaths`, `isweqtoforallpathsAxiom`, `toforallpaths`, `isweqhomot`, `twooutof3c`,
and anything else from UniMath.Foundations.UnivalenceAxiom.*)

(* Exercise 1 *)

(* Define the category of sets. *)

Lemma Set_precategory_ob_mor : precategory_ob_mor.
Proof.
  use tpair.
  - exact hSet.
  - simpl.
    intros x y.
    exact (x→ y).
Defined.

(*This was proven in homework 2*)
Theorem prop_thm {P : UU} : isaprop P <-> (∏ x y : P, x = y).
(* The different definitions of isaprop are logically equivalent. *)
Proof.
Admitted.

(*Staat op https://unimath.github.io/doc/UniMath/c26d11b/UniMath.MoreFoundations.Univalence.html*)
Lemma funextsec_toforallpaths {T : UU} {P : T → UU} {f g : ∏ t : T, P t} :
  ∏ (h : f = g), funextsec _ _ _ (toforallpaths _ _ _ h) = h.
Proof.
  intro h.
  exact (!homotinvweqweq0 (weqtoforallpaths _ _ _) h).
Defined.

Lemma Homsetisaset {a b:hSet}: isaset(a→ b).
Proof.
  unfold hSet in a.
  unfold hSet in b.
  induction a as [A pa].
  induction b as [B pb].
  unfold isaset.
  intros f g.
  apply prop_thm.
  intros e h.
  rewrite (pathsinv0 (funextsec_toforallpaths e)).
    rewrite (pathsinv0 (funextsec_toforallpaths h)).
  apply (maponpaths (funextsec (λ _ : A, B) f g)).
  cbn.
  set (e2:=toforallpaths (λ _ : A, B) f g e).
  set (h2:=toforallpaths (λ _ : A, B) f g h).
  unfold homot in e2.
  unfold homot in h2.
  apply funextsec.
  intro x.
  apply pb.
Defined.
  

Theorem set_category : category.
Proof.
  use tpair.
  - use tpair.
    + use tpair.
      * exact Set_precategory_ob_mor.
      * cbn.
        unfold precategory_id_comp.
        split.
        -- intro c.
           cbn.
           cbn in c.
           exact (idfun c).
        -- intros.
           unfold Set_precategory_ob_mor in X.
           cbn in X.
           unfold Set_precategory_ob_mor in X0.
           cbn in X0.
           exact (X0∘X).
    + unfold is_precategory.
      split.
      ** split.
           --- intros.
               use funextsec.
               intro x.
               cbn.
               apply idpath.
           --- intros.
               use funextsec.
               intro x.
               cbn.
               apply idpath.
     ** split.
        *** intros.
            use funextsec.
            intro x.
            cbn.
            apply idpath.
        *** intros.
            use funextsec.
            intro x.
            cbn.
            apply idpath.
  - cbn.
    unfold has_homsets.
    intros.
    cbn.
    apply Homsetisaset.
Defined.

(* Exercise 2 *)

(* Show that the category from exercise 1 is univalent.*)

Definition setiso (S T : hSet) : UU :=
  ∑ f : S → T ,
  ∑ g : T → S ,
  g ∘ f ~ idfun S
  ×
  f ∘ g ~ idfun T.

Definition set_idtoiso (S T : hSet) : (S = T) → (setiso S T).
Proof.
  intro e.
  induction e.
  use tpair.
  - exact (idfun S).
  - use tpair.
    + exact (idfun S).
    + split.
      * intro s.
        simpl.
        apply idpath.
      * intro s.
        simpl.
        apply idpath.
Defined.

Theorem set_univalence (S T : hSet) : isweq (set_idtoiso S T).
Proof.
  Admitted.
  (* You don't have to fill this proof in; it is from previous exercises.*)

Lemma inbetweenstep (a b:hSet): (∑ (f : a → b) (g : b → a), g ∘ f ~ idfun a × f ∘ g ~ idfun b)→ (  ∑ (f : a → b) (g : b → a), g ∘ f = idfun a × f ∘ g = idfun b).
Proof.
  intro S.
  induction S as [f [g p]].
  use tpair.
  - exact f.
  - use tpair.
    + exact g.
    + induction p as [p1 p2].
      set (q1:= (funextsec (λ _ :a, a) (g∘f) (idfun a)) p1).
      set (q2:= (funextsec (λ _ :b, b) (f∘g) (idfun b)) p2).
      exact (q1,, q2).
Defined.

Lemma inbetweenstep_isweq (a b:hSet): isweq(inbetweenstep a b).
Proof.
  use isweq_iso.
  - intro S.
    induction S as [f [g p]].
    use tpair.
    + exact f.
    + use tpair.
      * exact g.
      * induction p as [p1 p2].
        set (q1:=(toforallpaths (λ _ :a, a) (g∘f) (idfun a)) p1).
        set (q2:=(toforallpaths (λ _ :b, b) (f∘g) (idfun b)) p2).
        exact (q1,,q2).
  - intro S.
    induction S as [f [g p]].
    cbn.
    use total2_paths2_f.
    -- use idpath.
    -- cbn.
       use total2_paths2_f.
       ** use idpath.
       ** cbn.
          induction p as [p1 p2].
          cbn.
          use total2_paths2_f.
          --- apply funextsec.
              induction a as [A pa].
              induction b as [B pb].
              cbn.
              intro x.
              apply pa.
          --- cbn.
              apply funextsec.
              induction a as [A pa].
              induction b as [B pb].
              cbn.
              intro y.
              apply pb.
  - intro S.
    induction S as [f [g p]].
    cbn.
    use total2_paths2_f.
    *** apply idpath.
    *** use total2_paths2_f.
        ---- apply idpath.
        ---- cbn.
             induction p as [p1 p2].
             use total2_paths2_f.
             **** apply Homsetisaset.
             **** apply Homsetisaset.
Defined.          
      
Lemma commutativediagram (a b:set_category): (inbetweenstep a b)∘ (set_idtoiso a b)=(λ p:a=b, idtoiso p).
Proof.
  unfold inbetweenstep.
  use funextsec.
  intro e.
  induction e.
  cbn.
  unfold identity_z_iso.
  unfold identity_is_z_iso.
  cbn.
  apply idpath.
Defined.


Theorem set : univalent_category.
Proof.
  unfold univalent_category.
  use tpair.
  - exact set_category.
  - cbn.
    unfold is_univalent.
    intros.
    set (U:=set_univalence a b).
    rewrite (pathsinv0 (commutativediagram a b)).
    use twooutof3c.
    + exact U.
    + exact (inbetweenstep_isweq a b).
Defined.
    

(* Exercise 3 *)
(* Define the interval HIT, and use it to show that every homotopy induces an
   equality of functions *)
   
(** Generalisation of [maponpaths] to dependent functions. *)
(** Called [apd] in the lecture *)
Definition maponpaths_dep {X:UU} {Y : X -> UU}
    (f : ∏ x:X, Y x) {x1 x2} (e : x1 = x2)
  : transportf _ e (f x1) = f x2.
Proof.
  induction e. apply idpath.
Defined.   

Definition interval_ind_structure {I:UU} {s:I} {t:I} (e:s=t) : UU
  :=  ∏ (P:I→ UU) (p_s: P s) (p_t:P t) (p_e: transportf _ e p_s=p_t),
∑ (f : ∏ x:I, P x) (e_s : f s = p_s) (e_t: f t=p_t), 
       maponpaths_dep f e
     = maponpaths _ e_s @ p_e @ !e_t.

(** From now on, we fix an interval type *)
Context {I : UU} {s : I} {t:I} (e : s = t)
  (interval_str : interval_ind_structure e).

Definition constantfunction (A B:UU): A→ UU.
Proof.
  intro a.
  exact B.
Defined.

Lemma constantfunction_behaves (A B:UU) (a1 a2:A) (e: a1=a2) (b:B): transportf (constantfunction A B) e b=b.
Proof.
  induction e.
  unfold constantfunction.
  cbn.
  apply idpath.
Defined.

Lemma simplified_int_structure (B:UU): ∏ (b_s:B) (b_t:B) (b_e:b_s=b_t), 
      ∑ (f: I→ B) (e_s: f s=b_s) (e_t: f t=b_t),
      maponpaths f e = e_s @ b_e @ !e_t.
Proof.
   intros.
   set (S:= (constantfunction_behaves I B s t e b_s)).
   set (E:= S@ b_e).
   set (M:= interval_str (constantfunction I B) b_s b_t E).
   cbn in M.
   induction M as [f [e_s [e_t h]]].
   cbn in h.
   use tpair.
   - exact f.
   - cbn.
     use tpair.
     + exact e_s.
     + use tpair.
       * exact e_t.
       * cbn.
         induction e_s.
         induction e_t.
         induction e.
         cbn.
         cbn in h.
         apply h.
Defined.

Lemma interval_to_paths (A B:UU) (f g:A→ B): f ~ g→ (A→ (I→B)).
Proof.
  intro h.
  intro a.
  set (ha:= h a).
  set (F:= simplified_int_structure B (f a) (g a) (ha)).
  induction F as [F0 _].
  exact F0.
Defined.

Lemma interval_to_functions (A B:UU) (f g:A→ B): f ~ g→ (I→ A→ B).
Proof.
  intro h.
  intro i.
  intro a.
  set (F:=interval_to_paths A B f g h).
  exact (F a i).
Defined.
  
Lemma Source_to_f_with_funext {A B:UU} (f g:A→ B) (h:f ~ g): ((interval_to_functions A B f g h) s)=f.
Proof.
  unfold interval_to_functions.
  unfold interval_to_paths.
  cbn.
  (*If we were allowed to use funext we could do the following.*)
  use funextsec.
  intro a.
  set (T:= interval_str (constantfunction I B) (f a) (g a) (((constantfunction_behaves I B s t e) (f a)) @ h a)).
  induction T as [F [e_s _]].
  apply e_s.
  (*However since we want to prove funext by the end of this exercise, I don't think I should be allowed to use funext. Without funext though I don't know how to prove this statement.*)
Defined.

Lemma Source_to_f_without_funext {A B:UU} (f g:A→ B) (h:f ~ g): ((interval_to_functions A B f g h) s)=f.
Proof.
  unfold interval_to_functions.
  unfold interval_to_paths.
  cbn.
Admitted.

Lemma Target_to_f_with_funext {A B:UU} (f g:A→ B) (h:f ~ g): ((interval_to_functions A B f g h) t)=g.
Proof.
  unfold interval_to_functions.
  unfold interval_to_paths.
  cbn.
  (*If we were allowed to use funext we could do the following.*)
  use funextsec.
  intro a.
  set (T:= interval_str (constantfunction I B) (f a) (g a) (((constantfunction_behaves I B s t e) (f a)) @ h a)).
  induction T as [F [e_s [e_t _]]].
  apply e_t.
  (*However since we want to prove funext by the end of this exercise, I don't think I should be allowed to use funext. Without funext though I don't know how to prove this statement.*)
Defined.

Lemma Target_to_f_without_funext {A B:UU} (f g:A→ B) (h:f ~ g): ((interval_to_functions A B f g h) t)=g.
Proof.
  unfold interval_to_functions.
  unfold interval_to_paths.
  cbn.
Admitted.


Theorem homotopy_induces_equality {A B:UU}: ∏ f g:A→ B, f ~ g → f=g.
Proof.
  intros.
  set (F:= interval_to_functions A B f g X).
  set (E:=maponpaths F e).
  set (sE:=Source_to_f_with_funext f g X).
  set (tE:=Target_to_f_with_funext f g X).
  set (E2:=!sE@E@tE).
  apply E2.
Defined.

(* Exercise 4 *)

(* Do not do this one in Unimath, only in LaTeX. *)

(* Consider the category G of groupoids, and the class D ⊆ mor (G) of isofibrations. Show that this is a display map category, and that it has the two additional properties required of a display map category. That is, show that:
  i) every X → * is a display map
  ii) D is closed under isomorphisms
  iii) D is stable under pullback
  iv) D contains all isomorphisms
  v) D is closed under composition

  Use the definition for isofibration and any results from the nLab page https://ncatlab.org/nlab/show/isofibration. Hint: use Prop 3.1.
  *)
