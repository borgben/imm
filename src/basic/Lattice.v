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

(* Direct parenthood relative to allocated elements. The child may be fresh. *)
Definition parent_of {A : Type} (L : lattice A)
    (allocated : list A) (parent child : A) : Prop :=
  In parent allocated /\
  lt L parent child /\
  ~ (exists z, In z allocated /\ lt L z child /\ lt L parent z).

(* The strict downset of x restricted to allocated elements. *)
Definition strict_downset {A : Type}
    (L : lattice A) (allocated : list A) (x y : A) : Prop :=
  In y allocated /\ lt L y x.

(* The strict downset together with x itself. *)
Definition downset {A : Type}
    (L : lattice A) (allocated : list A) (x y : A) : Prop :=
  strict_downset L allocated x y \/ x = y.

(* A maximal allocated element has no strictly greater allocated element. *)
Definition maximal {A : Type} (L : lattice A)
    (allocated : list A) (x : A) : Prop :=
  In x allocated /\ forall y, In y allocated -> le L x y -> y = x.

Record fresh_child_lattice (A : Type) := {
  uid_lattice : lattice A;
  allocated: list A;
  allocated_bottom : In (bottom uid_lattice) allocated;
  (* The concrete allocation invariant supplies this order-theoretic property. *)
  allocated_join_prime : forall y p q,
    In y allocated -> In p allocated -> In q allocated ->
    le uid_lattice y (join uid_lattice p q) ->
    le uid_lattice y p \/ le uid_lattice y q;

  (* Every UID has a finite strict causal past. *)
  finite_strict_lower : forall u, exists predecessors : list A,
    forall v, lt uid_lattice v u -> In v predecessors;


  (* Generate a fresh child of an already allocated parent. *)
  fresh_child : forall parent : A, In parent allocated -> A;

  (* The specification for fresh, restricting the definition of the "fresh_child_function". *)
  fresh_child_spec : forall parent (parent_allocated : In parent allocated),
    let child := fresh_child parent parent_allocated in
    parent_of uid_lattice allocated parent child  /\ 
    ~ In child allocated /\
    (forall y, downset uid_lattice allocated parent y <->
      strict_downset uid_lattice allocated child y);

  (* Fresh meet children, takes a parent element and generates two elements whos combined strict downset is the downset of their parent. *)
  fresh_meet_children : forall parent:A, In parent allocated -> (A * A); 

  fresh_meet_children_spec: forall parent (parent_allocated: In parent allocated), 
    let (child1, child2) := fresh_meet_children parent parent_allocated in
    incomparable uid_lattice child1 child2 /\  
    parent_of uid_lattice allocated parent child1 /\ parent_of uid_lattice allocated parent child2 /\ 
    ~ In child1 allocated /\ ~ In child2 allocated /\
    (forall y, downset uid_lattice allocated parent y <->
      strict_downset uid_lattice allocated child1 y /\
      strict_downset uid_lattice allocated child2 y);

  (* Fresh join child takes two parents and generates a child who's strict downset is the combined downsets of its parents *)
  fresh_join_child: forall parent1 parent2:A, incomparable uid_lattice parent1 parent2 -> In parent1 allocated -> In parent2 allocated -> A; 

  fresh_join_child_spec: 
    forall 
      (parent1 parent2:A) 
      (incomparable_parent1_parent2: incomparable uid_lattice parent1 parent2) 
      (parent1_allocated: In parent1 allocated) 
      (parent2_allocated: In parent2 allocated)
      (parent1_maximal : maximal uid_lattice allocated parent1)
      (parent2_maximal : maximal uid_lattice allocated parent2), 
    let child := @fresh_join_child parent1 parent2 incomparable_parent1_parent2  parent1_allocated parent2_allocated in 
    parent_of uid_lattice allocated parent1 child /\ parent_of uid_lattice allocated parent2 child /\ ~ In child allocated /\
    (forall y, strict_downset uid_lattice allocated child y <->
      downset uid_lattice allocated parent1 y \/ downset uid_lattice allocated parent2 y);
}.

(* Siblings are distinct identifiers with a common direct parent. *)
Definition sibling {A : Type} (L : fresh_child_lattice A) (x y : A) : Prop := 
  x <> y /\ exists parent, parent_of (uid_lattice L) (allocated L) parent x /\ parent_of (uid_lattice L) (allocated L) parent y.

End Lattice.
