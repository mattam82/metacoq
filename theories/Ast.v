Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.

Definition universe := positive.
Definition ident := string.

Inductive sort : Set :=
| sProp
| sSet
| sType (_ : universe).

Inductive sort_family : Set :=
| InProp | InSet | InType.

Inductive name : Set :=
| nAnon
| nNamed (_ : ident).

Inductive cast_kind : Set :=
| VmCast
| NativeCast
| Cast
| RevertCast.

Inductive inductive : Set :=
| mkInd : string -> nat -> inductive.

Record def (term : Set) : Set := mkdef
{ dname : name (** the name (note, this may mention other definitions **)
; dtype : term
; dbody : term (** the body (a lambda term) **)
; rarg  : nat  (** the index of the recursive argument, 0 for cofixpoints **)
}.

Definition mfixpoint (term : Set) : Set :=
  list (def term).

Definition projection : Set := inductive * nat (* params *) * nat (* argument *).

Inductive term : Set :=
| tRel       : nat -> term
| tVar       : ident -> term (** For free variables (e.g. in a goal) *)
| tMeta      : nat -> term   (** NOTE: this can go away *)
| tEvar      : nat -> list term -> term
| tSort      : sort -> term
| tCast      : term -> cast_kind -> term -> term
| tProd      : name -> term (** the type **) -> term -> term
| tLambda    : name -> term (** the type **) -> term -> term
| tLetIn     : name -> term (** the term **) -> term (** the type **) -> term -> term
| tApp       : term -> list term -> term
| tConst     : string -> term
| tInd       : inductive -> term
| tConstruct : inductive -> nat -> term
| tCase      : (inductive * nat) (* # of parameters *) -> term (** type info **) -> term ->
               list (nat * term) -> term
| tProj      : projection -> term -> term
| tFix       : mfixpoint term -> nat -> term
| tCoFix     : mfixpoint term -> nat -> term.

Record inductive_body :=
  mkinductive_body
    { ind_name : ident;
      ind_type : term; (* Closed arity *)
      ind_kelim : list sort_family; (* Allowed elimination sorts *)
      ind_ctors : list (ident * term (* Under context of arities of the mutual inductive *)
                    * nat (* arity, w/o lets, w/o parameters *));
      ind_projs : list (ident * term) (* names and types of projections, if any.
                                     Type under context of params and inductive object *) }.

Inductive program : Set :=
| PConstr : string -> term (* type *) -> term (* body *) -> program -> program
| PType   : ident -> nat (* # of parameters, w/o let-ins *) ->
            list inductive_body (* Non-empty *) -> program -> program
| PAxiom  : ident -> term (* the type *) -> program -> program
| PIn     : term -> program.


(** representation of mutual inductives. nearly copied from Coq/kernel/entries.mli
*)

Record one_inductive_entry : Set := {
  mind_entry_typename : ident;
  mind_entry_arity : term;
  mind_entry_template : bool; (* template polymorphism ? *)
  mind_entry_consnames : list ident;
  mind_entry_lc : list term}.


Inductive local_entry : Set := 
| LocalDef : term -> local_entry (* local let binding *)
| LocalAssum : term -> local_entry.


Inductive recursivity_kind :=
  | Finite (** = inductive *)
  | CoFinite (** = coinductive *)
  | BiFinite (** = non-recursive, like in "Record" definitions *).


(* kernel/entries.mli*)
Record mutual_inductive_entry : Set := {
  mind_entry_record : option (option ident); 
  mind_entry_finite : recursivity_kind;
  mind_entry_params : list (ident * local_entry);
  mind_entry_inds : list one_inductive_entry;
  mind_entry_polymorphic : bool; 
(*  mind_entry_universes : Univ.universe_context; *)
  mind_entry_private : option bool
}.


Record constant_decl :=
  { cst_name : ident;
    cst_type : term;
    cst_body : option term }.

Record minductive_decl :=
  { ind_npars : nat;
    ind_bodies : list inductive_body }.

Inductive global_decl :=
| ConstantDecl : ident -> constant_decl -> global_decl
| InductiveDecl : ident -> minductive_decl -> global_decl.

Definition extend_program (p : program) (d : global_decl) : program :=
  match d with
  | ConstantDecl i {| cst_name:=_;  cst_type:=ty;  cst_body:=Some body |}
    => PConstr i ty body p
  | ConstantDecl i {| cst_name:=_;  cst_type:=ty;  cst_body:=None |}
    => PAxiom i ty p
  | InductiveDecl i {| ind_npars:=n; ind_bodies := l |}
    => PType i n l p
  end.
