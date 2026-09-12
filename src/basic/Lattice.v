Require Import List.

Set Implicit Arguments.

Module Lattice.


Record lattice (A : Type) := {
  le : A -> A -> Prop;
  meet : A -> A -> A;
  join : A -> A -> A;
  bottom : A;

  bottom_le : forall x, le bottom x;
  le_refl : forall x, le x x;
  le_trans : forall x y z, le x y -> le y z -> le x z;
  le_antisym : forall x y, le x y -> le y x -> x = y;

  meet_spec : forall x y z, le z (meet x y) <-> (le z x /\ le z y);
  join_spec : forall x y z, le (join x y) z <-> (le x z /\ le y z)
}.

Definition lt {A : Type} (L : lattice A) (x y : A) : Prop := le L x y /\ x <> y.

Definition incomparable {A : Type} (L : lattice A) (x y : A) : Prop := ~ le L x y /\ ~ le L y x.

Record fresh_child_lattice (A : Type) := {
  tid_lattice : lattice A;

  (* Defines what it means to be a direct parent *)
  parent_of : A -> A -> Prop;
  
  (* Given some A and a list of already allocated A's generates a "fresh" A*)
  fresh_child : A -> list A -> A;

  (* The specification for fresh, restricting the definition of the "fresh_child_function". *)
  fresh_child_spec : forall parent allocated,
    let child := fresh_child parent allocated in
    parent_of parent child /\ lt tid_lattice parent child /\ ~ In child allocated /\
    (forall other, In other allocated ->
       parent_of parent other ->
        incomparable tid_lattice child other)

}.

(* Siblings are distinct identifiers with a common direct parent. *)
Definition sibling {A : Type} (L : fresh_child_lattice A) (x y : A) : Prop := 
  x <> y /\ exists parent, parent_of L parent x /\ parent_of L parent y.

End Lattice.
