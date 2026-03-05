Unset Universe Checking.
Require Export UniMath.Foundations.All.

(* Exercise 1 *)

(* Formulate the following statements from Rijke in type theory (you do not have to prove them). The answer to the first one (a) is given as an example. *)

(* 1a. Theorem 9.3.4 *)

Definition Eq_Σ {A : UU} {B : A → UU}: (∑ x : A, B x) → (∑ x : A, B x) → UU.
Proof.
  Admitted.

Definition pair_eq {A : UU} {B : A → UU} (s t : ∑ x : A, B(x)) : (s = t) → Eq_Σ s t.
Proof.
  Admitted.

Theorem Thm_9_3_4 {A : UU} {B : A → UU} (s t : ∑ x : A, B(x)) : isweq (pair_eq s t).
Proof.
  Admitted.

(* 1b. Exercise 9.2a *)
Theorem constant_b: bool → bool→ bool.
Proof.
      intro b.
      intro c.
      exact b.
Defined.

Theorem Ex_9_2_a {b: bool}: (isweq (constant_b b))→ empty.
Admitted.
(* 1c. Exercise 9.4a *)
Theorem Ex9_4a_1 {A B X: UU} {f: A→ X} {g:B→ X} {h: A→ B} {s: B→ A}: (f~g∘ h)× (h∘ s~ idfun B)→(g~f∘ s).
Proof.
  Admitted.
Theorem Ex9_4a_2 {A B X: UU} {f: A→ X} {g:B→ X} {h: A→ B} {s: B→ A}: (f~g∘ h)× (h∘ s~ idfun B)→ ((∑ F:X→ A,f∘ F~ idfun X)<->(∑ G:X→ B,g∘ G~ idfun X)).
Proof.
  Admitted.
(* 1d. Exercise 9.9a *)
Theorem exponent_k {X:UU}: (X→ X)→ nat → (X→ X).
Proof.
  intro f.
  intro k.
  induction k.
  - exact (idfun X).
  - exact (f∘ IHk).
Defined.
Theorem Ex_9_9_a {X:UU} {f:X→ X}: (∏ x y: X, ∑ k:nat, exponent_k f k x=y)→ isweq f.
Proof.
  Admitted.

(**************************************************************)

(* From here on, all `Admitted.`s should be filled in. *)

(* Exercise 2 *)

(* Here we give a solution to Exercise 3 from the last homework, so that you can prove something about it in this Exercise.*)
Theorem exp : nat → nat → nat.
Proof.
  intros n m.
  induction m.
  - exact 1.
  - exact (IHm * n).
Defined.

Search (∏ X Y : UU, ∏ f : X → Y, ∏ x y : X, x = y → (f x) = (f y)).

Search (∏ a b c : nat, (a * b) * c = a * (b * c)).
Search (∏ a b : nat, a * b = b * a).
(* This command searches the library for functions of this kind. You should see in the output that ~maponpaths~ is of this kind. You can then print ~maponpaths~ (i.e. write "Print maponpaths.") to see the definition.

You can use this to find other lemmas from the library. You can use any facts without proof from the library about addition and multiplication as well as ~maponpaths~.*)



Theorem exp_hom {l m n : nat} : exp l (m + n) = (exp l m) * (exp l n).
(* `exp l` takes addition to multiplication.*)
Proof.
  induction m.
  - simpl.
    apply idpath.
  - simpl.
    rewrite IHm.
    rewrite natmultassoc.
    apply pathsinv0.
    rewrite natmultassoc.
    apply maponpaths.
    rewrite natmultcomm.
    apply idpath.
Defined.

(* Exercise 3 *)

Lemma path_combination {A : UU} {a a' b : A} (p : a = b) (q: a' = b) : a = a'.
(* Another way to combine paths. *)
Proof.
  rewrite p.
  rewrite q.
  apply idpath.
Defined.

(* Exercise 4 *)

Lemma path_combination_fact {A : UU} {a b : A} (p : a = b) : idpath a = path_combination p p.
(* Check that the above way of combining paths does the `right thing'. *)
Proof.
   rewrite p.
   simpl.
   apply idpath.
Defined.
  


(* Exercise 5 *)

(* isaprop is defined differently in UniMath than we in class in lecture 5. (It will become clear later why.) We haven't learned yet what isofhlevel means, but we do know what iscontr means. *)

Check isaprop.
Print isaprop.
Lemma trivial_prop_lem (P : UU) : isaprop P = ∏ x y : P, iscontr (x = y).
Proof.
  unfold isaprop.
  unfold isofhlevel.
  apply idpath.
Defined.

Theorem prop_thm {P : UU} : isaprop P <-> (∏ x y : P, x = y).
(* The different definitions of isaprop are logically equivalent. *)
Proof.
  unfold isaprop.
  unfold isofhlevel.
  split.
  - intro a.
    apply a.
  - intro b.
    intro x.
    intro y.
    unfold iscontr.
    apply (λ f (p:P), f p).
    -- intro p.
       use tpair.
       + set (v:= b x p).
         set (w:= b y p).
         exact (path_combination v w).
       + cbn.
         intro t.
         induction t.
         apply path_combination_fact.
     -- exact x.
Defined.         
        
    
     

(* Exercise 6 *)

(* NB: The prefered defintion of equivalence in the UniMath library is `isweq`: it says the fibers are contractible.
You are allowed to use isweq_iso from the library in this proof: it says if f is a quasiequivalence, then f is an equivalence in that sense.*)


Theorem inverse {A B : UU} (e : A ≃ B) : B → A.
Proof.
    unfold weq in e.
    induction e as [f w].
    intro b.
    unfold isweq in w.
    unfold iscontr in w.
    induction (w b) as [cntr _].
    unfold hfiber in cntr.
    induction cntr as [x _].
    exact x.
Defined.

Theorem prop_equiv_to_log_equiv (P Q : hProp) : (P ≃ Q) <-> (P <-> Q).
(* An equivalence between propositions is (logically equivalent to) a logical equivalence. *)
Proof.
  split.
  - intro h.
    split.
    + apply h.
    + apply (inverse h).
  - intro k.
    induction k as [f g].
    unfold weq.
    use tpair.
      + apply f.
      + apply (isweq_iso f g).
      --intro x.
        unfold hProp in P.
        induction P as [E F].
        apply F.
      --intro y.
        unfold hProp in Q.
        induction Q as [M N].
        apply N.
Defined.
        
      
  
