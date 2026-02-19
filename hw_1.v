Require Export UniMath.Foundations.All.

(* Exercise 1 *)

Theorem comp_app { P Q R : UU } (f : P → Q) (g : Q → R) (p : P) : R.
Proof.
  set (q:= f p).
  set (r:= g q).
  exact r.
Defined.
(* Exercise 2 *)

Theorem curried_proj {P Q R : UU} : (P → (Q × R)) → (P → Q).
Proof.
  intro f.
  intro p.
  set (c:= f p).
  induction c as [q r].
  exact q.
Qed.
  

(* Exercise 3 *)

Theorem exp : nat → nat → nat.
Proof.
  intro n.
  intro m.
  induction m.
  - exact 1.
  - set (q:= n*IHm).
    exact q.
Defined.


Compute (exp 5 1).
(* Should output 5. *)

Compute (exp 3 2).
(* Should output 9. *)

(* Exercise 4 *)

Search (∏ X Y : UU, ∏ f : X → Y, ∏ x y : X, x = y → (f x) = (f y)).

(* This command searches the library for functions of this type. You should see in the output that ~maponpaths~ is of this type. You can then print ~maponpaths~ (i.e. write "Print maponpaths.") to see the definition.

You can use this to find other lemmas from the library. You can use any facts without proof from the library about addition and multiplication as well as ~maponpaths~.*)

Search (∏ a b c : nat, (a * b) * c = a * (b * c)).

Theorem exp_hom {l m n : nat} : exp l (m + n) = (exp l m) * (exp l n).
Proof.
  induction m.
  - simpl.
    apply idpath.
  - simpl.
    rewrite IHm.
    rewrite natmultassoc.
    apply idpath.
Defined.
