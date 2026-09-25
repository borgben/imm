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
  uid_lattice : lattice A;
  allocated: list A;

  (* The strict downset of x restricted to allocated elements. *)
  strict_downset : A -> A -> Prop :=
    fun x y => In y allocated /\ lt uid_lattice y x;

  (* The elements of the downset are the elements of the strict downset and 'x'. *)
  downset : A -> A -> Prop :=
    fun x y => strict_downset x y \/ x = y;

  (* Every UID has a finite strict causal past. *)
  finite_strict_lower : forall u, exists predecessors : list A,
    forall v, lt uid_lattice v u -> In v predecessors;

  (* Defines what it means to be a direct parent *)
  parent_of : A -> A -> Prop := (fun parent child => lt uid_lattice parent child /\ ~(exists z, lt uid_lattice z child /\ lt uid_lattice parent z)); 
  
  (* Generate a fresh child of an already allocated parent. *)
  fresh_child : forall parent : A, In parent allocated -> A;

  (* The specification for fresh, restricting the definition of the "fresh_child_function". *)
  fresh_child_spec : forall parent (parent_allocated : In parent allocated),
    let child := fresh_child parent parent_allocated in
    parent_of parent child  /\ 
    ~ In child allocated /\
    downset parent = strict_downset child;

  (* Fresh meet children, takes a parent element and generates two elements whos combined strict downset is the downset of their parent. *)
  fresh_meet_children : forall parent:A, In parent allocated -> (A * A); 

  fresh_meet_children_spec: forall parent (parent_allocated: In parent allocated), 
    let (child1, child2) := fresh_meet_children parent parent_allocated in
    incomparable uid_lattice child1 child2 /\  
    parent_of parent child1 /\ parent_of parent child2 /\ 
    ~ In child1 allocated /\ ~ In child2 allocated /\
    downset parent = fun y => (strict_downset child1) y /\  (strict_downset child2) y; 

  (* Fresh join child takes two parents and generates a child who's strict downset is the combined downsets of its parents *)
  fresh_join_child: forall parent1 parent2:A, incomparable uid_lattice parent1 parent2 -> In parent1 allocated -> In parent2 allocated -> A; 

  fresh_join_child_spec: forall (parent1 parent2:A) (incomparable_parent1_parent2: incomparable uid_lattice parent1 parent2) (parent1_allocated: In parent1 allocated) (parent2_allocated: In parent2 allocated), 
    let child := @fresh_join_child parent1 parent2 incomparable_parent1_parent2  parent1_allocated parent2_allocated in 
    parent_of parent1 child /\ parent_of parent2 child /\ ~ In child allocated /\  strict_downset child = fun y => (downset parent1) y \/  (downset parent2) y;
}.

(* Siblings are distinct identifiers with a common direct parent. *)
Definition sibling {A : Type} (L : fresh_child_lattice A) (x y : A) : Prop := 
  x <> y /\ exists parent, parent_of L parent x /\ parent_of L parent y.

End Lattice.
