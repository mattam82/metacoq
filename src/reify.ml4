(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

open Ltac_plugin

let contrib_name = "template-coq"
open Feedback


let toDecl (old: Names.name * ((Constr.constr) option) * Constr.constr) : Context.Rel.Declaration.t =
  let (name,value,typ) = old in 
  match value with
  | Some value -> Context.Rel.Declaration.LocalDef (name,value,typ)
  | None -> Context.Rel.Declaration.LocalAssum (name,typ)

let fromDecl (n: Context.Rel.Declaration.t) :  Names.name * ((Constr.constr) option) * Constr.constr =
  match n with 
  | Context.Rel.Declaration.LocalDef (name,value,typ) -> (name,Some value,typ)
  | Context.Rel.Declaration.LocalAssum (name,typ) -> (name,None,typ)

let cast_prop = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname = "Casting of propositions in template-coq";
  Goptions.optkey = ["Template";"Cast";"Propositions"];
  Goptions.optread = (fun () -> !cast_prop);
  Goptions.optwrite = (fun a -> cast_prop:=a);
}

(* whether Set Template Cast Propositions is on, as needed for erasure in Certicoq *)
let is_cast_prop () = !cast_prop                     
                     
let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)

module TermReify =
struct
  exception NotSupported of Term.constr * string

  module Cmap = Names.KNmap
  module Cset = Names.KNset
  module Mindset = Names.Mindset

  (* flags *)
  let opt_hnf_ctor_types = ref false
  let opt_debug = ref false

  let with_debug f =
    opt_debug := true ;
    try
      let result = f () in
      opt_debug := false ;
      result
    with
      e -> let _ = opt_debug := false in raise e

  let debug (m : unit -> Pp.std_ppcmds) =
    if !opt_debug then
      Feedback.(msg_debug (m ()))
    else
      ()

  let with_hnf_ctor_types f =
    opt_hnf_ctor_types := true ;
    try
      let result = f () in
      opt_hnf_ctor_types := false ;
      result
    with
      e -> let _ = opt_hnf_ctor_types := false in raise e

  open Pp (* this adds the ++ to the current scope *)

  let not_supported trm =
    (* Feedback.msg_error (str "Not Supported:" ++ spc () ++ Printer.pr_constr trm) ; *)
    CErrors.user_err (str "Not Supported:" ++ spc () ++ Printer.pr_constr trm)
    (* raise (NotSupported (trm, "no reason")) *)

  let not_supported_verb trm rs =
    CErrors.user_err (str "Not Supported raised at " ++ str rs ++ str ":" ++ spc () ++ Printer.pr_constr trm)
    
  let bad_term trm =
    raise (NotSupported (trm, "bad term"))

  let bad_term_verb trm rs =
    raise (NotSupported (trm, "bad term because of " ^ rs))

    
  let gen_constant_in_modules locstr dirs s =
    Universes.constr_of_global (Coqlib.gen_reference_in_modules locstr dirs s)

  let resolve_symbol (path : string list) (tm : string) : Term.constr =
    gen_constant_in_modules contrib_name [path] tm

  let pkg_bignums = ["Coq";"Numbers";"BinNums"]
  let pkg_datatypes = ["Coq";"Init";"Datatypes"]
  let pkg_reify = ["Template";"Ast"]
  let pkg_string = ["Coq";"Strings";"String"]

  let r_reify = resolve_symbol pkg_reify

  let tstring = resolve_symbol pkg_string "string"
  let tString = resolve_symbol pkg_string "String"
  let tEmptyString = resolve_symbol pkg_string "EmptyString"
  let tO = resolve_symbol pkg_datatypes "O"
  let tS = resolve_symbol pkg_datatypes "S"
  let tnat = resolve_symbol pkg_datatypes "nat"
  let ttrue = resolve_symbol pkg_datatypes "true"
  let cSome = resolve_symbol pkg_datatypes "Some"
  let cNone = resolve_symbol pkg_datatypes "None"
  let tfalse = resolve_symbol pkg_datatypes "false"
  let unit_tt = resolve_symbol pkg_datatypes "tt"
  let tAscii = resolve_symbol ["Coq";"Strings";"Ascii"] "Ascii"
  let c_nil = resolve_symbol pkg_datatypes "nil"
  let c_cons = resolve_symbol pkg_datatypes "cons"
  let prod_type = resolve_symbol pkg_datatypes "prod"
  let sum_type = resolve_symbol pkg_datatypes "sum"
  let option_type = resolve_symbol pkg_datatypes "option"
  let bool_type = resolve_symbol pkg_datatypes "bool"
  let cInl = resolve_symbol pkg_datatypes "inl"
  let cInr = resolve_symbol pkg_datatypes "inr"
  let prod a b =
    Term.mkApp (prod_type, [| a ; b |])
  let c_pair = resolve_symbol pkg_datatypes "pair"
  let pair a b f s =
    Term.mkApp (c_pair, [| a ; b ; f ; s |])

    (* reify the constructors in Template.Ast.v, which are the building blocks of reified terms *)
  let nAnon = r_reify "nAnon"
  let nNamed = r_reify "nNamed"
  let kVmCast = r_reify "VmCast"
  let kNative = r_reify "NativeCast"
  let kCast = r_reify "Cast"
  let kRevertCast = r_reify "RevertCast"
  let sProp = r_reify "sProp"
  let sSet = r_reify "sSet"
  let sType = r_reify "sType"
  let tident = r_reify "ident"
  let tIndTy = r_reify "inductive"
  let tmkInd = r_reify "mkInd"
  let (tTerm,tRel,tVar,tMeta,tEvar,tSort,tCast,tProd,
       tLambda,tLetIn,tApp,tCase,tFix,tConstructor,tConst,tInd,tUnknown) =
    (r_reify "term", r_reify "tRel", r_reify "tVar", r_reify "tMeta", r_reify "tEvar",
     r_reify "tSort", r_reify "tCast", r_reify "tProd", r_reify "tLambda",
     r_reify "tLetIn", r_reify "tApp", r_reify "tCase", r_reify "tFix",
     r_reify "tConstruct", r_reify "tConst", r_reify "tInd", r_reify "tUnknown")

  let tlevel = r_reify "level"
  let tLevel = r_reify "Level"
  let tLevelVar = r_reify "LevelVar"
      
  let (tdef,tmkdef) = (r_reify "def", r_reify "mkdef")
  let (tLocalDef,tLocalAssum,tlocal_entry) = (r_reify "LocalDef", r_reify "LocalAssum", r_reify "local_entry")

  let (cFinite,cCoFinite,cBiFinite) = (r_reify "Finite", r_reify "CoFinite", r_reify "BiFinite")
  let (pConstr,pType,pAxiom,pIn) =
    (r_reify "PConstr", r_reify "PType", r_reify "PAxiom", r_reify "PIn")
  let tinductive_body = r_reify "inductive_body"
  let tmkinductive_body = r_reify "mkinductive_body"

  let tMutual_inductive_entry = r_reify "mutual_inductive_entry"
  let tOne_inductive_entry = r_reify "one_inductive_entry"
  let tBuild_mutual_inductive_entry = r_reify "Build_mutual_inductive_entry"
  let tBuild_one_inductive_entry = r_reify "Build_one_inductive_entry"
  
  let (tmReturn,tmBind,tmQuote,tmQuoteTermRec,tmReduce,tmMkDefinition,tmMkInductive, tmPrint, tmQuoteTerm) =
    (r_reify "tmReturn", r_reify "tmBind", r_reify "tmQuote", r_reify "tmQuoteTermRec", r_reify "tmReduce",
       r_reify "tmMkDefinition", r_reify "tmMkInductive", r_reify "tmPrint", r_reify "tmQuoteTerm")

  let to_positive =
    let xH = resolve_symbol pkg_bignums "xH" in
    let xO = resolve_symbol pkg_bignums "xO" in
    let xI = resolve_symbol pkg_bignums "xI" in
    let rec to_positive n =
      if n = 1 then
	xH
      else
	if n mod 2 = 0 then
	  Term.mkApp (xO, [| to_positive (n / 2) |])
	else
  	  Term.mkApp (xI, [| to_positive (n / 2) |])
    in
    fun n ->
      if n <= 0
      then raise (Invalid_argument ("to_positive: " ^ string_of_int n))
      else to_positive n

  let to_coq_list typ =
    let the_nil = Term.mkApp (c_nil, [| typ |]) in
    let rec to_list (ls : Term.constr list) : Term.constr =
      match ls with
	[] -> the_nil
      | l :: ls ->
	Term.mkApp (c_cons, [| typ ; l ; to_list ls |])
    in to_list

  let int_to_nat =
    let cache = Hashtbl.create 10 in
    let rec recurse i =
      try Hashtbl.find cache i
      with
	Not_found ->
	  if i = 0 then
	    let result = tO in
	    let _ = Hashtbl.add cache i result in
	    result
	  else
	    let result = Term.mkApp (tS, [| recurse (i - 1) |]) in
	    let _ = Hashtbl.add cache i result in
	    result
    in
    fun i ->
      assert (i >= 0) ;
      recurse i

  let quote_bool b =
    if b then ttrue else tfalse

  let quote_char i =
    Term.mkApp (tAscii, Array.of_list (List.map (fun m -> quote_bool ((i land m) = m))
					 (List.rev [128;64;32;16;8;4;2;1])))

  let chars = Array.init 255 quote_char

  let quote_char c = chars.(int_of_char c)

  let string_hash = Hashtbl.create 420

  let to_string s =
    let len = String.length s in
    let rec go from acc =
      if from < 0 then acc
      else
        let term = Term.mkApp (tString, [| quote_char (String.get s from) ; acc |]) in
        go (from - 1) term
    in
    go (len - 1) tEmptyString
                      
  let quote_string s =
    try Hashtbl.find string_hash s
    with Not_found ->
      let term = to_string s in
      Hashtbl.add string_hash s term; term

  let quote_ident i =
    let s = Names.string_of_id i in
    quote_string s

  let quote_name n =
    match n with
      Names.Name id -> Term.mkApp (nNamed, [| quote_ident id |])
    | Names.Anonymous -> nAnon

  let quote_cast_kind k =
    match k with
      Term.VMcast -> kVmCast
    | Term.DEFAULTcast -> kCast
    | Term.REVERTcast -> kRevertCast
    | Term.NATIVEcast -> kNative

  let string_of_level s =
    to_string (Univ.Level.to_string s)

  let quote_level s =
    match Univ.Level.var_index s
    with Some x -> Term.mkApp (tLevelVar, [| int_to_nat x |])
       | None -> Term.mkApp (tLevel, [| string_of_level s|])

  let quote_universe s =
    match Univ.Universe.level s with
      Some x -> string_of_level x
    | None -> to_string ""

  let quote_sort s =
    match s with
      Term.Prop _ ->
	if s = Term.prop_sort then sProp
	else
	  let _ = assert (s = Term.set_sort) in
	  sSet
    | Term.Type u -> Term.mkApp (sType, [| quote_universe u |])

  let quote_inductive env (t : Names.inductive) =
    let (m,i) = t in
    Term.mkApp (tmkInd, [| quote_string (Names.string_of_kn (Names.canonical_mind m))
                	 ; int_to_nat i |])
               
  let mk_ctor_list =
    let ctor_list =
      let ctor_info_typ = prod (prod tident tTerm) tnat in
      to_coq_list ctor_info_typ
    in
    fun ls ->
    let ctors = List.map (fun (a,b,c) -> pair (prod tident tTerm) tnat
					 (pair tident tTerm a b) c) ls in
      Term.mkApp (tmkinductive_body, [| ctor_list ctors |])

  let rec pair_with_number st ls =
    match ls with
      [] -> []
    | l :: ls -> (st,l) :: pair_with_number (st + 1) ls

  let hnf_type env ty =
    let rec hnf_type continue ty =
      match Term.kind_of_term ty with
	Term.Prod (n,t,b) -> Term.mkProd (n,t,hnf_type true b)
      | Term.LetIn _
      | Term.Cast _
      | Term.App _ when continue ->
	 hnf_type false (Reduction.whd_all env ty)
      | _ -> ty
    in
    hnf_type true ty

  let push_rel decl (in_prop, env) = (in_prop, Environ.push_rel decl env)
  let push_rel_context ctx (in_prop, env) = (in_prop, Environ.push_rel_context ctx env)

let castSetProp (sf:Term.sorts) t =
  let sf = Term.family_of_sort sf in
  if sf == Term.InProp 
  then Term.mkApp (tCast, [| t ; kCast ; Term.mkApp (tSort, [| sProp |]) |])
  else if sf == Term.InSet 
  then Term.mkApp (tCast, [| t ; kCast ; Term.mkApp (tSort, [| sSet |]) |])
  else t

let noteTypeAsCast t typ =
  Term.mkApp (tCast, [| t ; kCast ; typ |])

let getSort env (t:Term.constr) =
  Retyping.get_sort_of env Evd.empty (EConstr.of_constr t)

let getType env (t:Term.constr) : Term.constr =
  EConstr.to_constr Evd.empty (Retyping.get_type_of env Evd.empty (EConstr.of_constr t))

(* given a term of shape \x1 x2 ..., T, it puts a cast around T if T is a Set or a Prop,
lambdas like this arise in the case-return type in matches, i.e. the part between return and with in
match _  as _ in  _ return __ with *)
let rec putReturnTypeInfo (env : Environ.env) (t: Term.constr) : Term.constr =
  match Term.kind_of_term t with
      | Term.Lambda (n,t,b) ->
          Term.mkLambda (n,t,putReturnTypeInfo (Environ.push_rel (toDecl (n, None, t)) env) b)
      | _ ->
          let sf =  (getSort env t)  in 
          Term.mkCast (t,Term.DEFAULTcast,Term.mkSort sf)

  let quote_univ_instance pu =
    to_coq_list tlevel (Array.to_list (Array.map quote_level (Univ.Instance.to_array pu)))

  open Declarations
  let abstract_inductive_instance iu =
    match iu with
    | Monomorphic_ind ctx -> Univ.Instance.empty
    | Polymorphic_ind ctx ->
       let ctx = Univ.instantiate_univ_context ctx in
       Univ.UContext.instance ctx
    | Cumulative_ind cumi ->
       let cumi = Univ.instantiate_cumulativity_info cumi in
       let ctx = Univ.CumulativityInfo.univ_context cumi in
       Univ.UContext.instance ctx
  let constant_instance = function
    | Monomorphic_const _ -> Univ.Instance.empty
    | Polymorphic_const ctx ->
       let ctx = Univ.instantiate_univ_context ctx in
       Univ.UContext.instance ctx

  let quote_term_remember
      (add_constant : Names.kernel_name -> 'a -> 'a)
      (add_inductive : Names.inductive -> 'a -> 'a) =
    let rec quote_term (acc : 'a) env trm =
      let aux acc env trm =
      match Term.kind_of_term trm with
	Term.Rel i -> (Term.mkApp (tRel, [| int_to_nat (i - 1) |]), acc)
      | Term.Var v -> (Term.mkApp (tVar, [| quote_ident v |]), acc)
      | Term.Sort s -> (Term.mkApp (tSort, [| quote_sort s |]), acc)
      | Term.Cast (c,k,t) ->
	let (c',acc) = quote_term acc env c in
	let (t',acc) = quote_term acc env t in
	(Term.mkApp (tCast, [| c' ; quote_cast_kind k ; t' |]), acc)
      | Term.Prod (n,t,b) ->
	let (t',acc) = quote_term acc env t in
  let sf = getSort (snd env)  t in
  let env = push_rel (toDecl (n, None, t)) env in
  let sfb = getSort (snd env) b in
	let (b',acc) = quote_term acc env b in
	(Term.mkApp (tProd, [| quote_name n ; castSetProp sf  t' ; castSetProp sfb b' |]), acc)
      | Term.Lambda (n,t,b) ->
	let (t',acc) = quote_term acc env t in
  let sf = getSort (snd env) t  in 
	let (b',acc) = quote_term acc (push_rel (toDecl (n, None, t)) env) b in
       (Term.mkApp (tLambda, [| quote_name n ; castSetProp sf t' ; b' |]), acc)
      | Term.LetIn (n,e,t,b) ->
	let (e',acc) = quote_term acc env e in
	let (t',acc) = quote_term acc env t in
	let (b',acc) = quote_term acc (push_rel (toDecl (n, Some e, t)) env) b in
	(Term.mkApp (tLetIn, [| quote_name n ; e'; t' ; b' |]), acc)
      | Term.App (f,xs) ->
	let (f',acc) = quote_term acc env f in
	let (xs',acc) =
	  List.fold_left (fun (xs,acc) x ->
	    let (x,acc) = quote_term acc env x in (x :: xs, acc))
	    ([],acc) (Array.to_list xs) in
	(Term.mkApp (tApp, [| f' ; to_coq_list tTerm (List.rev xs') |]), acc)
      | Term.Const (c,pu) -> (* FIXME: take universe constraints into account *)
         let kn = Names.Constant.canonical c in 
	 (Term.mkApp (tConst, [| quote_string (Names.string_of_kn kn)
                              ;  quote_univ_instance pu                               
                              |]),
          add_constant kn acc)
      | Term.Construct ((ind,c),pu) ->
         (* FIXME: take universe constraints into account *)
	(Term.mkApp (tConstructor, [| quote_inductive env ind ; int_to_nat (c - 1) ; quote_univ_instance pu |]), add_inductive ind acc)
      | Term.Ind (i,pu) -> (* FIXME: take universe constraints into account *)
         (Term.mkApp (tInd, [| quote_inductive env i ; quote_univ_instance pu |]),
          add_inductive i acc)
      | Term.Case (ci,typeInfo,discriminant,e) ->
        let ind = quote_inductive env ci.Term.ci_ind in
        let npar = int_to_nat ci.Term.ci_npar in
        let info = pair tIndTy tnat ind npar in
  let discriminantType = getType (snd env) discriminant in
  let typeInfo = putReturnTypeInfo (snd env) typeInfo in
	let (qtypeInfo,acc) = quote_term acc env typeInfo in
	let (discriminant,acc) = quote_term acc env discriminant in
  let (discriminantType,acc) = (quote_term acc env discriminantType) in
  let discriminant = noteTypeAsCast discriminant discriminantType in 
	let (branches,acc) =
          CArray.fold_left2 (fun (xs,acc) x nargs ->
            let (x,acc) = quote_term acc env x in
            let t = pair tnat tTerm (int_to_nat nargs) x in
              (t :: xs, acc))
          ([],acc) e ci.Term.ci_cstr_nargs in
        let tl = prod tnat tTerm in
        (Term.mkApp (tCase, [| info ; qtypeInfo ; discriminant ; to_coq_list tl (List.rev branches) |]),
         acc)
      | Term.Fix fp ->
	let (t,n,acc) = quote_fixpoint acc env fp in
	(Term.mkApp (tFix, [| t ; int_to_nat n |]), acc)
      | _ -> (Term.mkApp (tUnknown, [| quote_string (Format.asprintf "%a" pp_constr trm) |]), acc)
      in
      let in_prop, env' = env in 
      if is_cast_prop () && not in_prop then
        let ty = Retyping.get_type_of env' Evd.empty (EConstr.of_constr trm) in
        let sf = Retyping.get_sort_family_of env' Evd.empty ty in
        if sf == Term.InProp then
          aux acc (true, env')
              (Term.mkCast (trm, Term.DEFAULTcast,
                            Term.mkCast (EConstr.to_constr Evd.empty ty, Term.DEFAULTcast, Term.mkProp))) 
        else aux acc env trm
      else aux acc env trm
    and quote_fixpoint acc env t =
      let ((a,b),(ns,ts,ds)) = t in
      let rec seq f t =
	if f < t then
	  f :: seq (f + 1) t
	else
	  []
      in
      let ctxt = CArray.map2_i (fun i na t -> (Context.Rel.Declaration.LocalAssum (na, Vars.lift i t))) ns ts in
      let envfix = push_rel_context (Array.to_list ctxt) env in
      let mk_fun (xs,acc) i =
	let n = int_to_nat (Array.get a i) in
	let nm = quote_name (Array.get ns i) in
	let (ty,acc) = quote_term acc env (Array.get ts i) in
	let (ds,acc) = quote_term acc envfix (Array.get ds i) in
	(Term.mkApp (tmkdef, [| tTerm ; nm ; ty ; ds ; n |]) :: xs, acc)
      in
      let (defs,acc) = List.fold_left mk_fun ([],acc) (seq 0 (Array.length a)) in
      (to_coq_list (Term.mkApp (tdef, [| tTerm |])) (List.rev defs), b, acc)
    and quote_minductive_type (acc : 'a) env (t : Names.mutual_inductive) =
      let mib = Environ.lookup_mind t (snd env) in
      let inst = abstract_inductive_instance mib.Declarations.mind_universes in
      let indtys =
        Array.to_list Declarations.(Array.map (fun oib ->
           let ty = Inductive.type_of_inductive (snd env) ((mib,oib),inst) in
           (Context.Rel.Declaration.LocalAssum (Names.Name oib.mind_typename, ty))) mib.mind_packets)
      in
      let envind = push_rel_context indtys env in
      let (ls,acc) =
	List.fold_left (fun (ls,acc) (n,oib) ->
	  let named_ctors =
	    CList.combine3
	      Declarations.(Array.to_list oib.mind_consnames)
	      Declarations.(Array.to_list oib.mind_user_lc)
	      Declarations.(Array.to_list oib.mind_consnrealargs)
	  in
	  let (reified_ctors,acc) =
	    List.fold_left (fun (ls,acc) (nm,ty,ar) ->
	      debug (fun () -> Pp.(str "XXXX" ++ spc () ++
                            bool !opt_hnf_ctor_types)) ;
	      let ty = if !opt_hnf_ctor_types then hnf_type (snd envind) ty else ty in
	      let (ty,acc) = quote_term acc envind ty in
	      ((quote_ident nm, ty, int_to_nat ar) :: ls, acc))
	      ([],acc) named_ctors
	  in
	  Declarations.((quote_ident oib.mind_typename,
	    mk_ctor_list (List.rev reified_ctors)) :: ls, acc))
	  ([],acc) Declarations.(pair_with_number 0
		      (Array.to_list mib.mind_packets))
      in
      let params = int_to_nat mib.Declarations.mind_nparams in
      (params, to_coq_list (prod tident tinductive_body)
	 (List.map (fun (a,b) ->
	   pair tident tinductive_body a b) (List.rev ls)),
       acc)
    in ((fun acc env -> quote_term acc (false, env)),
        (fun acc env -> quote_minductive_type acc (false, env)))

  let quote_term env trm =
    let (fn,_) = quote_term_remember (fun _ () -> ()) (fun _ () -> ()) in
    fst (fn () env trm)

  type defType =
    Ind of Names.inductive
  | Const of Names.kernel_name

  let quote_term_rec env trm =
    let visited_terms = ref Names.KNset.empty in
    let visited_types = ref Mindset.empty in
    let constants = ref [] in
    let add quote_term quote_type trm acc =
      match trm with
      | Ind (mi,idx) ->
	let t = mi in
	if Mindset.mem t !visited_types then ()
	else
	  begin
	    let (params,result,acc) = quote_type acc env mi in
	    let ref_name =
	      quote_string (Names.string_of_kn (Names.canonical_mind mi)) in
	    visited_types := Mindset.add t !visited_types ;
	    constants := Term.mkApp (pType, [| ref_name; params
					     ; result |]) :: !constants
	  end
      | Const kn ->
	if Names.KNset.mem kn !visited_terms then ()
	else
	  begin
	    visited_terms := Names.KNset.add kn !visited_terms ;
            let c = Names.Constant.make kn kn in
	    let cd = Environ.lookup_constant c env in
	    let do_body body pu =
	      let (result,acc) =
		quote_term acc (Global.env ()) body
	      in
	      constants := Term.mkApp (pConstr,
				       [| quote_string (Names.string_of_kn kn)
                                        ; quote_univ_instance pu                        
				       ; result |]) :: !constants
	    in
	    Declarations.( 
	      match cd.const_body, cd.const_universes with
		Undef _, _ ->
		begin
		  let (ty,acc) =
		    match cd.const_type with
		    | RegularArity ty -> quote_term acc (Global.env ()) ty
		    | TemplateArity _ -> assert false
		  in
		  constants := Term.mkApp (pAxiom,
					   [| quote_string (Names.string_of_kn kn) ; ty |]) :: !constants
		end
	      | Def cs, pu ->
		do_body (Mod_subst.force_constr cs) (constant_instance pu)
	      | OpaqueDef lc, pu ->
		do_body (Opaqueproof.force_proof (Global.opaque_tables ()) lc) (constant_instance pu))
	  end
    in
    let (quote_rem,quote_typ) =
      let a = ref (fun _ _ _ -> assert false) in
      let b = ref (fun _ _ _ -> assert false) in
      let (x,y) =
	quote_term_remember (fun x () -> add !a !b (Const x) ())
	                    (fun y () -> add !a !b (Ind y) ())
      in
      a := x ;
      b := y ;
      (x,y)
    in
    let (x,acc) = quote_rem () env trm
    in List.fold_left (fun acc x -> Term.mkApp (x, [| acc |]))
                      (Term.mkApp (pIn, [| x |])) !constants

 let to_coq_bool b = if b then ttrue else tfalse

 let quote_one_ind envA envC (mi:Entries.one_inductive_entry) : Term.constr =
   Declarations.(
     Entries.(
   let iname = quote_ident mi.mind_entry_typename  in
   let arity = quote_term envA mi.mind_entry_arity in 
   let templatePoly = to_coq_bool mi.mind_entry_template in
   let consnames = to_coq_list tident (List.map quote_ident (mi.mind_entry_consnames)) in
   let cons_types = to_coq_list tTerm (List.map (quote_term envC) (mi.mind_entry_lc)) in
   Term.mkApp (tBuild_one_inductive_entry, [| iname; arity; templatePoly; consnames; cons_types |])))

let process_local_entry 
  (f: 'a -> Term.constr option (* body *) -> Term.constr (* type *) -> Names.Id.t -> Environ.env -> 'a) 
  ((env,a):(Environ.env*'a)) 
  ((n,le):(Names.Id.t * Entries.local_entry))
  :  (Environ.env * 'a) =
  match le with
  | Entries.LocalAssumEntry t -> (Environ.push_rel (toDecl (Names.Name n,None,t)) env, f a None t n env)
  | Entries.LocalDefEntry b -> 
      let typ = getType env b in
      (Environ.push_rel (toDecl (Names.Name n, Some b, typ)) env, f a (Some b) typ n env)


let quote_mind_params env (params:(Names.Id.t * Entries.local_entry) list)
  :  Environ.env*(Term.constr list)=
  let pair i l = pair tident tlocal_entry i l in 
  let f lr ob t n env =
    match ob with
    | Some b ->  (pair (quote_ident n) (Term.mkApp (tLocalDef,[|(quote_term env b)|])))::lr
    | None -> 
      let sf = getSort env t  in 
       (pair (quote_ident n) (Term.mkApp (tLocalAssum,[|castSetProp sf (quote_term env t)|])))::lr in
    let (env, params) = List.fold_left (process_local_entry f) (env,[]) (List.rev params) in (env, List.rev params)
    
let mind_params_as_types ((env,t):Environ.env*Term.constr) (params:(Names.Id.t * Entries.local_entry) list) : 
   Environ.env*Term.constr =
    List.fold_left (process_local_entry (fun tr ob typ n env -> Term.mkProd_or_LetIn (toDecl (Names.Name n,ob,typ)) tr)) (env,t) 
      (List.rev params)

let quote_mind_finiteness (f: Decl_kinds.recursivity_kind) =
  match f with
  | Decl_kinds.Finite -> cFinite
  | Decl_kinds.CoFinite -> cCoFinite
  | Decl_kinds.BiFinite -> cBiFinite
     
let quote_mut_ind  env (mi:Declarations.mutual_inductive_body) : Term.constr =
   let t= Discharge.process_inductive ([],Univ.AUContext.empty) (Names.Cmap.empty,Names.Mindmap.empty) mi in
   Declarations.(
     Entries.(
   let the_prod = Term.mkApp (prod_type,[|tident; tlocal_entry|]) in 
   let mr = Term.mkApp (cNone, [|Term.mkApp (option_type, [|tident|])|])  in
   let mf = quote_mind_finiteness t.mind_entry_finite in 
   let mp = to_coq_list the_prod (snd (quote_mind_params env (t.mind_entry_params))) in
   (* before quoting the types of constructors, we need to enrich the environment with the inductives *)
   let one_arities =
      List.map 
        (fun x -> (x.mind_entry_typename,
           snd (mind_params_as_types (env,x.mind_entry_arity) (t.mind_entry_params)))) 
      t.mind_entry_inds in
  (* env for quoting constructors of inductives. First push inductices, then params *)
   let envC = List.fold_left (fun env p -> Environ.push_rel (toDecl (Names.Name (fst p), None, snd p)) env) env (one_arities) in
   let (envC,_) = List.fold_left (process_local_entry (fun _ _ _ _ _ -> ())) (envC,()) (List.rev (t.mind_entry_params)) in
  (* env for quoting arities of inductives -- just push the params *)
   let (envA,_) = List.fold_left (process_local_entry (fun _ _ _ _ _ -> ())) (env,()) (List.rev (t.mind_entry_params)) in
   let is = to_coq_list tOne_inductive_entry (List.map (quote_one_ind envA envC) (t.mind_entry_inds)) in
   let mpol = tfalse in
   let mpr = Term.mkApp (cNone, [|bool_type|]) in
   Term.mkApp (tBuild_mutual_inductive_entry, [| mr; mf; mp; is; mpol; mpr |]);
  ))

  let split_name s : (Names.DirPath.t * Names.Id.t)=
    let ss = List.rev (Str.split (Str.regexp (Str.quote ".")) s) in
    match ss with
      nm :: rst ->
    	let dp = (Names.make_dirpath (List.map Names.id_of_string rst)) in (dp, Names.Id.of_string nm)
    | [] -> raise (Failure "Empty name cannot be quoted")

  let kn_of_canonical_string s =
    let ss = List.rev (Str.split (Str.regexp (Str.quote ".")) s) in
    match ss with
      nm :: rst ->
	let to_mp ls = Names.MPfile (Names.make_dirpath (List.map Names.id_of_string ls)) in
	let mp = to_mp rst in
	Names.make_kn mp Names.empty_dirpath (Names.mk_label nm)
    | _ -> assert false

 let quote_decl bypass env evm (name:string) =
   let opType = Term.mkApp(sum_type, [|tTerm;tMutual_inductive_entry|]) in
   let mkSome c t = Term.mkApp (cSome, [|opType; Term.mkApp (c, [|tTerm;tMutual_inductive_entry; t|] )|]) in
   let mkSomeDef = mkSome cInl in
   let mkSomeInd  = mkSome cInr in
   let (dp, nm) = split_name name in
(*   try *)
         Feedback.msg_debug (Pp.str("finding Inductive"));
   match Nametab.locate (Libnames.make_qualid dp nm) with
   |Globnames.ConstRef c ->
      let cd = Environ.lookup_constant c env in
	    Declarations.(
	      match cd.const_body with
		    | Undef _ -> Term.mkApp (cNone, [|opType|])
	      | Def cs -> mkSomeDef (quote_term (Global.env ()) (Mod_subst.force_constr cs))
	      | OpaqueDef cs -> 
      if bypass 
      then mkSomeDef (quote_term (Global.env ()) (Opaqueproof.force_proof (Global.opaque_tables ()) cs))
      else Term.mkApp (cNone, [|opType|])
      )
    | Globnames.IndRef ni ->
        let c = Environ.lookup_mind (fst ni) env in (* FIX: For efficienctly, we should also export (snd ni)*)
         Feedback.msg_debug (Pp.str("found Inductive"));
        let miq = quote_mut_ind env c in
        mkSomeInd miq
    | Globnames.ConstructRef _ -> Term.mkApp (cNone, [|opType|]) (* FIX: return the enclusing mutual inductive *)
    | Globnames.VarRef _ -> (* what is this *)Term.mkApp (cNone, [|opType|])
(*    with 
    Not_found -> 
          Term.mkApp (cNone, [|opType|])   *)

  let rec app_full (trm:Term.constr) acc =
    match Term.kind_of_term trm with
      Term.App (f, xs) -> app_full f (Array.to_list xs @ acc)
    | _ -> (trm, acc)

  let rec nat_to_int trm =
    let (h,args) = app_full trm [] in
    if Term.eq_constr h tO then
      0
    else if Term.eq_constr h tS then
      match args with
	n :: _ -> 1 + nat_to_int n
      | _ -> not_supported_verb trm "nat_to_int nil"
    else
      not_supported_verb trm "nat_to_int"

  let from_bool trm =
    if Term.eq_constr trm ttrue then
      true
    else if Term.eq_constr trm tfalse then
      false
    else not_supported_verb trm "from_bool"

  let unquote_char trm =
    let (h,args) = app_full trm [] in
    if Term.eq_constr h tAscii then
      match args with
	a :: b :: c :: d :: e :: f :: g :: h :: _ ->
	  let bits = List.rev [a;b;c;d;e;f;g;h] in
	  let v = List.fold_left (fun a n -> (a lsl 1) lor if from_bool n then 1 else 0) 0 bits in
	  char_of_int v
      | _ -> assert false
    else
      not_supported trm
(*
let reduce_all env (evm,def) =
  	let (evm2,red) = Tacinterp.interp_redexp env evm (Genredexpr.Cbv Redops.all_flags) in
	  let red = fst (Redexpr.reduction_of_red_expr env red) in
	  red env evm2 def
*)

  let reduce_hnf env (evm,(def:Term.constr)) =
    (evm,EConstr.to_constr Evd.empty (Tacred.hnf_constr env evm (EConstr.of_constr def))) 

  let reduce_all env (evm,(def:Term.constr))  =
     (evm,EConstr.to_constr Evd.empty (Redexpr.cbv_vm env evm (EConstr.of_constr def)))

  let unquote_string trm =
    let rec go n trm =
      let (h,args) = app_full trm [] in
      if Term.eq_constr h tEmptyString then
        Bytes.create n
      else if Term.eq_constr h tString then
	match args with
	  c :: s :: _ ->
	    let res = go (n + 1) s in
	    let _ = Bytes.set res n (unquote_char c) in
	    res
	| _ -> bad_term_verb trm "unquote_string"
      else
	not_supported_verb trm "unquote_string"
    in
    Bytes.to_string (go 0 trm)

  let unquote_ident trm =
    Names.id_of_string (unquote_string trm)

  let unquote_cast_kind trm =
    if Term.eq_constr trm kVmCast then
      Term.VMcast
    else if Term.eq_constr trm kCast then
      Term.DEFAULTcast
    else if Term.eq_constr trm kRevertCast then
      Term.REVERTcast
    else if Term.eq_constr trm kNative then
      Term.VMcast
    else
      bad_term trm


  let unquote_name trm =
    let (h,args) = app_full trm [] in
    if Term.eq_constr h nAnon then
      Names.Anonymous
    else if Term.eq_constr h nNamed then
      match args with
	n :: _ -> Names.Name (unquote_ident n)
      | _ -> raise (Failure "ill-typed, expected name")
    else
      raise (Failure "non-value")


  (* This code is taken from Pretyping, because it is not exposed globally *)
  let strict_universe_declarations = ref true
  let is_strict_universe_declarations () = !strict_universe_declarations
  let get_universe evd (loc, s) =
        let names, _ = Global.global_universe_names () in
        if CString.string_contains ~where:s ~what:"." then
          match List.rev (CString.split '.' s) with
          | [] -> CErrors.anomaly (str"Invalid universe name " ++ str s ++ str".")
          | n :: dp ->
	     let num = int_of_string n in
	     let dp = Names.DirPath.make (List.map Names.Id.of_string dp) in
	     let level = Univ.Level.make dp num in
	     let evd =
	       try Evd.add_global_univ evd level
	       with UGraph.AlreadyDeclared -> evd
	     in evd, level
        else
          try
	    let level = Evd.universe_of_name evd s in
	    evd, level
          with Not_found ->
	    try
	      let id = try Names.Id.of_string s with _ -> raise Not_found in
              evd, snd (Names.Idmap.find id names)
	    with Not_found ->
	      CErrors.user_err ?loc ~hdr:"interp_universe_level_name"
		            (Pp.(str "Undeclared universe: " ++ str s))
  (* end of code from Pretyping *)
                 
  let unquote_sort trm =
    let (h,args) = app_full trm [] in
    if Term.eq_constr h sType then
      match args with
        x :: _ -> let _, lvl = get_universe Evd.empty (None, unquote_string x) in
                  Term.sort_of_univ (Univ.Universe.make lvl)
      | _ -> bad_term_verb trm "no Type"
    else if Term.eq_constr h sProp then
      Term.prop_sort
    else if Term.eq_constr h sSet then
      Term.set_sort
    else
      raise (Failure "ill-typed, expected sort")



  let denote_inductive trm =
    let (h,args) = app_full trm [] in
    if Term.eq_constr h tmkInd then
      match args with
	nm :: num :: _ ->
        let s = (unquote_string nm) in
        let (dp, nm) = split_name s in
        (try 
          match Nametab.locate (Libnames.make_qualid dp nm) with
          | Globnames.ConstRef c ->  raise (Failure (String.concat "this not an inductive constant. use tConst instead of tInd : " [s]))
          | Globnames.IndRef i -> (fst i, nat_to_int  num)
          | Globnames.VarRef _ -> raise (Failure (String.concat "the constant is a variable. use tVar : " [s]))
          | Globnames.ConstructRef _ -> raise (Failure (String.concat "the constant is a consructor. use tConstructor : " [s]))
        with
        Not_found ->   raise (Failure (String.concat "Constant not found : " [s])))
      | _ -> assert false
    else
      raise (Failure "non-constructor")

  let rec from_coq_list trm =
    let (h,args) = app_full trm [] in
    if Term.eq_constr h c_nil then []
    else if Term.eq_constr h c_cons then
      match args with
	_ :: x :: xs :: _ -> x :: from_coq_list xs
      | _ -> bad_term trm
    else
      not_supported_verb trm "from_coq_list"




  (* let reduce_all env (evm,def) rd = *)
  (*   let (evm2,red) = Ltac_plugin.Tacinterp.interp_redexp env evm rd in *)
  (*   let red = fst (Redexpr.reduction_of_red_expr env red) in *)
  (*   let Sigma.Sigma (c, evm, _) = red.Reductionops.e_redfun env (Sigma.Unsafe.of_evar_map evm2) def in *)
  (*   Sigma.to_evar_map evm, c *)

  let from_coq_pair trm =
    let (h,args) = app_full trm [] in
    if Term.eq_constr h c_pair then
      match args with
	_ :: _ :: x :: y :: [] -> (x, y)
      | _ -> bad_term trm
    else
      not_supported_verb trm "from_coq_pair"

(*
Stm.interp
Vernacentries.interp
Vernacexpr.Check
*)

  (** NOTE: Because the representation is lossy, I should probably
   ** come back through elaboration.
   ** - This would also allow writing terms with holes
   **)
  let rec denote_term trm =
    debug (fun () -> Pp.(str "denote_term" ++ spc () ++ Printer.pr_constr trm)) ;
    let (h,args) = app_full trm [] in
    if Term.eq_constr h tRel then
      match args with
	x :: _ ->
	  Term.mkRel (nat_to_int x + 1)
      | _ -> raise (Failure "ill-typed")
    else if Term.eq_constr h tVar then
      match args with
	x :: _ -> Term.mkVar (unquote_ident x)
      | _ -> raise (Failure "ill-typed")
    else if Term.eq_constr h tSort then
      match args with
	x :: _ -> Term.mkSort (unquote_sort x)
      | _ -> raise (Failure "ill-typed")
    else if Term.eq_constr h tCast then
      match args with
	t :: c :: ty :: _ ->
	  Term.mkCast (denote_term t, unquote_cast_kind c, denote_term ty)
      | _ -> raise (Failure "ill-typed")
    else if Term.eq_constr h tProd then
      match args with
	n :: t :: b :: _ ->
	  Term.mkProd (unquote_name n, denote_term t, denote_term b)
      | _ -> raise (Failure "ill-typed (product)")
    else if Term.eq_constr h tLambda then
      match args with
	n :: t :: b :: _ ->
	Term.mkLambda (unquote_name n, denote_term t, denote_term b)
      | _ -> raise (Failure "ill-typed (lambda)")
    else if Term.eq_constr h tLetIn then
      match args with
	n :: e :: t :: b :: _ ->
	  Term.mkLetIn (unquote_name n, denote_term e, denote_term t, denote_term b)
      | _ -> raise (Failure "ill-typed (let-in)")
    else if Term.eq_constr h tApp then
      match args with
	f :: xs :: _ ->
	  Term.mkApp (denote_term f,
		      Array.of_list (List.map denote_term (from_coq_list xs)))
      | _ -> raise (Failure "ill-typed (app)")
    else if Term.eq_constr h tConst then
      match args with
    	s :: [] ->
        let s = (unquote_string s) in
        let (dp, nm) = split_name s in
        (try 
          match Nametab.locate (Libnames.make_qualid dp nm) with
          | Globnames.ConstRef c ->  Term.mkConst c
          | Globnames.IndRef _ -> raise (Failure (String.concat "the constant is an inductive. use tInd : " [s]))
          | Globnames.VarRef _ -> raise (Failure (String.concat "the constant is a variable. use tVar : " [s]))
          | Globnames.ConstructRef _ -> raise (Failure (String.concat "the constant is a consructor. use tConstructor : " [s]))
        with
        Not_found ->   raise (Failure (String.concat "Constant not found : " [s])))

      | _ -> raise (Failure "ill-typed (tConst)")
    else if Term.eq_constr h tConstructor then
      match args with
	i :: idx :: _ ->
	  let i = denote_inductive i in
	  Term.mkConstruct (i, nat_to_int idx + 1)
      | _ -> raise (Failure "ill-typed (constructor)")
    else if Term.eq_constr h tInd then
      match args with
	i :: _ ->
	  let i = denote_inductive i in
	  Term.mkInd i
      | _ -> raise (Failure "ill-typed (inductive)")
    else if Term.eq_constr h tCase then
      match args with
	info :: ty :: d :: brs :: _ ->
          let i, _ = from_coq_pair info in
          let ind = denote_inductive i in
          let ci = Inductiveops.make_case_info (Global.env ()) ind Term.RegularStyle in
          let denote_branch br =
            let _, br = from_coq_pair br in
            denote_term br
          in
	  Term.mkCase (ci, denote_term ty, denote_term d,
			Array.of_list (List.map denote_branch (from_coq_list brs)))
      | _ -> raise (Failure "ill-typed (case)")
    else if Term.eq_constr h tFix then
      match args with
	    bds :: i :: _ ->
        let unquoteFbd  b : ((Term.constr * Term.constr) * (Term.constr * Term.constr)) =
          let (_,args) = app_full b [] in
          match args with
          | _(*type*)::a::b::c::d::[] -> ((a,b),(c,d))
          |_ -> raise (Failure " (mkdef must take exactly 5 arguments)")
          in
        let lbd = List.map unquoteFbd (from_coq_list bds) in
        let (p1,p2) = (List.map fst lbd, List.map snd lbd) in
        let (names,types,bodies,rargs) = (List.map fst p1, List.map snd p1, List.map fst p2, List.map snd p2) in
        let (types,bodies) = (List.map denote_term types, List.map denote_term bodies) in
        let (names,rargs) = (List.map unquote_name names, List.map nat_to_int rargs) in
        let la = Array.of_list in
        Term.mkFix ((la rargs,nat_to_int i), (la names, la types, la bodies))
      | _ -> raise (Failure "tFix takes exactly 2 arguments")
    else
      not_supported_verb trm "big_case"

(*
  let declare_definition
    (id : Names.Id.t) (loc, boxed_flag, def_obj_kind)
    (binder_list : Constrexpr.local_binder list) red_expr_opt (constr_expr : Constrexpr.constr_expr)
    constr_expr_opt decl_hook =
    Command.do_definition
    id (loc, false, def_obj_kind) None binder_list red_expr_opt constr_expr
    constr_expr_opt decl_hook

  let add_definition name result =
    declare_definition name
	    (Decl_kinds.Global, false, Decl_kinds.Definition)
	    [] None result None (Lemmas.mk_hook (fun _ _ -> ()))
*)




  let unquote_red_add_definition b env evm name def =
	  let (evm,def) = reduce_all env (evm,def) in
  	let trm = if b then denote_term def else def in
    if b then Feedback.msg_debug ((Printer.pr_constr trm)) else ();
    Declare.declare_definition 
	  ~kind:Decl_kinds.Definition name
	  (trm, (* No new universe constraints can be generated by typing the AST *)
           Univ.ContextSet.empty)
	  
  let denote_local_entry trm =
    let (h,args) = app_full trm [] in
      match args with
	    x :: [] -> 
      if Term.eq_constr h tLocalDef then Entries.LocalDefEntry (denote_term x) 
      else (if  Term.eq_constr h tLocalAssum then Entries.LocalAssumEntry (denote_term x) else bad_term trm)
      | _ -> bad_term trm

  let denote_mind_entry_finite trm =
    let (h,args) = app_full trm [] in
      match args with
	    [] -> 
      if Term.eq_constr h cFinite then Decl_kinds.Finite
      else if  Term.eq_constr h cCoFinite then Decl_kinds.CoFinite
      else if  Term.eq_constr h cBiFinite then Decl_kinds.BiFinite
      else bad_term trm
      | _ -> bad_term trm

  let unquote_map_option f trm =
    let (h,args) = app_full trm [] in
    if Term.eq_constr h cSome then 
    match args with
	  _ :: x :: _ -> Some (f x)
      | _ -> bad_term trm
    else if Term.eq_constr h cNone then 
    match args with
	  _ :: [] -> None
      | _ -> bad_term trm
    else
      not_supported_verb trm "unqote_map_option"


  let declare_inductive (env: Environ.env) (evm: Evd.evar_map) (body: Term.constr) : unit =
  let open Entries in
  let (evm,body) = reduce_all env (evm, body)  (* (Genredexpr.Cbv Redops.all_flags) *) in
  let (_,args) = app_full body [] in (* check that the first component is Build_mut_ind .. *) 
  let one_ind b1 : Entries.one_inductive_entry = 
    let (_,args) = app_full b1 [] in (* check that the first component is Build_one_ind .. *)
    match args with
    | mt::ma::mtemp::mcn::mct::[] ->
    {
    mind_entry_typename = unquote_ident mt;
    mind_entry_arity = denote_term ma;
    mind_entry_template = from_bool mtemp;
    mind_entry_consnames = List.map unquote_ident (from_coq_list mcn);
    mind_entry_lc = List.map denote_term (from_coq_list mct)
    } 
    | _ -> raise (Failure "ill-typed one_inductive_entry")
     in 
  let mut_ind mr mf mp mi mpol mpr : Entries.mutual_inductive_entry =
    {
    mind_entry_record = unquote_map_option (unquote_map_option unquote_ident) mr;
    mind_entry_finite = denote_mind_entry_finite mf; (* inductive *)
    mind_entry_params = List.map (fun p -> let (l,r) = (from_coq_pair p) in (unquote_ident l, (denote_local_entry r))) 
      (List.rev (from_coq_list mp));
    mind_entry_inds = List.map one_ind (from_coq_list mi);
    (* mind_entry_polymorphic = from_bool mpol; *)
    mind_entry_universes =
      if from_bool mpol then
        (Polymorphic_ind_entry (snd (Evd.universe_context evm)))
      else Monomorphic_ind_entry (snd (Evd.universe_context evm));
    mind_entry_private = unquote_map_option from_bool mpr (*mpr*)
    } in 
    match args with
    mr::mf::mp::mi::mpol::mpr::[] -> 
      ignore(Command.declare_mutual_inductive_with_eliminations (mut_ind mr mf mp mi mpol mpr) [] [])
    | _ -> raise (Failure "ill-typed mutual_inductive_entry")

  let declare_interpret_inductive (env: Environ.env) (evm: Evd.evar_map) (body: Constrexpr.constr_expr) : unit =
	let (body,_) = Constrintern.interp_constr env evm body in
  declare_inductive env evm body

  let rec run_template_program_rec  ((env,evm,pgm): Environ.env * Evd.evar_map * Term.constr) : Environ.env * Evd.evar_map * Term.constr =
    let (evm,pgm) = reduce_hnf env (evm, pgm) in 
    let (coConstr,args) = app_full pgm [] in
    if Term.eq_constr coConstr tmReturn then
      match args with
      | _::h::[] -> (env,evm,h)
      | _ -> raise (Failure "tmReturn must take 2 arguments. Please file a bug with Template-Coq.")
    else if Term.eq_constr coConstr tmBind then
      match args with
      | _::_::a::f::[] ->
        let (env, evm, ar) = run_template_program_rec (env,evm,a) in
        run_template_program_rec (env,evm,(Term.mkApp (f, Array.of_list [ar])))
      | _ -> raise (Failure "tmBind must take 4 arguments. Please file a bug with Template-Coq.")
    else if Term.eq_constr coConstr tmMkDefinition then
      match args with
      | b::name::_::body::[] -> 
        let (evm,name) = reduce_all env (evm,name) in
        let (evm,b) = reduce_all env (evm,b) in
        let _ = unquote_red_add_definition (from_bool b) env evm (unquote_ident name) body in (env, evm, unit_tt)
      | _ -> raise (Failure "tmMkDefinition must take 4 arguments. Please file a bug with Template-Coq.")
    else if Term.eq_constr coConstr tmQuote then
      match args with
      | id::b::[] ->
          let (evm,id) = reduce_all env (evm,id) in
          let (evm,b) = reduce_all env (evm,b) in
          let qt=quote_decl (from_bool b) env evm (unquote_string id) in
          (env, evm, qt)
      | _ -> raise (Failure "tmQuote must take 1 argument. Please file a bug with Template-Coq.")
    else if Term.eq_constr coConstr tmQuoteTerm then
      match args with
      | _::trm::[] -> let qt = quote_term env trm in (* user should do the reduction (using tmReduce) if they want *)
              (env, evm, qt)
      | _ -> raise (Failure "tmQuoteTerm must take 1 argument. Please file a bug with Template-Coq.")
    else if Term.eq_constr coConstr tmQuoteTermRec then
      match args with
      | trm::[] -> let qt = quote_term_rec env trm in
              (env, evm, qt)
      | _ -> raise (Failure "tmQuoteTermRec must take 1 argument. Please file a bug with Template-Coq.")
    else if Term.eq_constr coConstr tmPrint then
      match args with
      | _::trm::[] -> let _ = Feedback.msg_debug ((Printer.pr_constr trm)) in (env, evm, unit_tt)
      | _ -> raise (Failure "tmPrint must take 2 arguments. Please file a bug with Template-Coq.")
    else if Term.eq_constr coConstr tmReduce then
      match args with
      | _(*reduction strategy*)::_(*type*)::trm::[] -> 
          let (evm,trm) = reduce_all env (evm,trm) in (env, evm, trm)
      | _ -> raise (Failure "tmReduce must take 3 arguments. Please file a bug with Template-Coq.")
    else if Term.eq_constr coConstr tmMkInductive then
      match args with
      | mind::[] -> let _ = declare_inductive env evm mind in (env, evm, unit_tt)
      | _ -> raise (Failure "tmReduce must take 3 arguments. Please file a bug with Template-Coq.")
    else raise (Failure "Invalid argument or yot yet implemented. The argument must be a TemplateProgram")

  let run_template_program (env: Environ.env) (evm: Evd.evar_map) (body: Constrexpr.constr_expr) : unit =
  	let (body,_) = Constrintern.interp_constr env evm body in
    let _ = run_template_program_rec (env,evm,body) in ()
end

DECLARE PLUGIN "template_plugin"

(** Stolen from CoqPluginUtils **)
(** Calling Ltac **)
let ltac_call tac (args:Tacexpr.glob_tactic_arg list) =
  Tacexpr.TacArg(Loc.tag @@ Tacexpr.TacCall (Loc.tag (Misctypes.ArgArg(Loc.tag @@ Lazy.force tac),args)))

(* let ltac_call tac (args:Tacexpr.glob_tactic_arg list) = *)
(*   Tacexpr.TacArg(Loc.ghost,Tacexpr.TacCall(Loc.ghost, Misctypes.ArgArg(Loc.ghost, Lazy.force tac),args)) *)

(* Calling a locally bound tactic *)
(* let ltac_lcall tac args = *)
(*   Tacexpr.TacArg(Loc.ghost,Tacexpr.TacCall(Loc.ghost, Misctypes.ArgVar(Loc.ghost, Names.id_of_string tac),args)) *)
let ltac_lcall tac args =
  Tacexpr.TacArg(Loc.tag @@ Tacexpr.TacCall (Loc.tag (Misctypes.ArgVar(Loc.tag @@ Names.Id.of_string tac),args)))

(* let ltac_letin (x, e1) e2 = *)
(*   Tacexpr.TacLetIn(false,[(Loc.ghost,Names.id_of_string x),e1],e2) *)

open Names
open Tacexpr
open Tacinterp
open Misctypes

   
let ltac_apply (f : Value.t) (args: Tacinterp.Value.t list) =
  let fold arg (i, vars, lfun) =
    let id = Names.Id.of_string ("x" ^ string_of_int i) in
    let x = Reference (ArgVar (Loc.tag id)) in
    (succ i, x :: vars, Id.Map.add id arg lfun)
  in
  let (_, args, lfun) = List.fold_right fold args (0, [], Id.Map.empty) in
  let lfun = Id.Map.add (Id.of_string "F") f lfun in
  let ist = { (Tacinterp.default_ist ()) with Tacinterp.lfun = lfun; } in
  Tacinterp.eval_tactic_ist ist (ltac_lcall "F" args)

(* let ltac_apply (f:Tacexpr.glob_tactic_expr) (args:Tacexpr.glob_tactic_arg list) = *)
(*   Tacinterp.eval_tactic *)
(*     (ltac_letin ("F", Tacexpr.Tacexp f) (ltac_lcall "F" args)) *)

let to_ltac_val c = Tacinterp.Value.of_constr c

let to_ltac_val c = Tacinterp.Value.of_constr c
(** From Containers **)
let declare_definition
    (id : Names.Id.t) (loc, boxed_flag, def_obj_kind)
    (binder_list) red_expr_opt constr_expr
    constr_expr_opt decl_hook =
  Command.do_definition
  id (loc, false, def_obj_kind) None binder_list red_expr_opt constr_expr
  constr_expr_opt decl_hook

let check_inside_section () =
  if Lib.sections_are_opened () then
    (** In trunk this seems to be moved to Errors **)
    (* For Coq 8.7: CErrors.user_err ~hdr:"Quote" (Pp.str "You can not quote within a section.") *)
    CErrors.user_err ~hdr:"Quote" (Pp.str "You can not quote within a section.")
  else ()

open Stdarg
open Tacarg
open Proofview.Notations
open Pp

TACTIC EXTEND get_goal
    | [ "quote_term" constr(c) tactic(tac) ] ->
      [ (** quote the given term, pass the result to t **)
  Proofview.Goal.nf_enter begin fun gl ->
          let env = Proofview.Goal.env gl in
	  let c = TermReify.quote_term env (EConstr.to_constr (Proofview.Goal.sigma gl) c) in
	  ltac_apply tac (List.map to_ltac_val [EConstr.of_constr c])
  end ]
(*
    | [ "quote_goal" ] ->
      [ (** get the representation of the goal **)
	fun gl -> assert false ]
    | [ "get_inductive" constr(i) ] ->
      [ fun gl -> assert false ]
*)
END;;

TACTIC EXTEND denote_term
    | [ "denote_term" constr(c) tactic(tac) ] ->
      [ Proofview.Goal.nf_enter begin fun gl ->
         let (evm,env) = Lemmas.get_current_context() in
         let c = TermReify.denote_term (EConstr.to_constr (Proofview.Goal.sigma gl) c) in
         let def' = Constrextern.extern_constr true env evm (EConstr.of_constr c) in
         let def = Constrintern.interp_constr env evm def' in
	 ltac_apply tac (List.map to_ltac_val [EConstr.of_constr (fst def)])
      end ]
END;;


VERNAC COMMAND EXTEND Make_vernac CLASSIFIED AS SIDEFF
    | [ "Quote" "Definition" ident(name) ":=" constr(def) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
	let def,uctx = Constrintern.interp_constr env evm def in
	let trm = TermReify.quote_term env def in
	ignore(Declare.declare_definition ~kind:Decl_kinds.Definition name
                                          (trm, Evd.evar_universe_context_set uctx)) ]
END;;

VERNAC COMMAND EXTEND Make_vernac_reduce CLASSIFIED AS SIDEFF
    | [ "Quote" "Definition" ident(name) ":=" "Eval" red_expr(rd) "in" constr(def) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
	let def, uctx = Constrintern.interp_constr env evm def in
        let evm = Evd.from_ctx uctx in
	let (evm2,def) = TermReify.reduce_all env (evm, def) in
	let trm = TermReify.quote_term env (def) in (* TODO: Check that this is evm2 *)
	ignore(Declare.declare_definition ~kind:Decl_kinds.Definition
                                          name (trm, Univ.ContextSet.empty)) ]
END;;

VERNAC COMMAND EXTEND Make_recursive CLASSIFIED AS SIDEFF
    | [ "Quote" "Recursively" "Definition" ident(name) ":=" constr(def) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
	let def = Constrintern.interp_constr env evm def in
	let trm = TermReify.quote_term_rec env (fst def) in
	ignore(Declare.declare_definition 
	  ~kind:Decl_kinds.Definition name
	  (trm, (* No new universe constraints can be generated by typing the AST *)
           Univ.ContextSet.empty)) ]
END;;

VERNAC COMMAND EXTEND Unquote_vernac CLASSIFIED AS SIDEFF
    | [ "Make" "Definition" ident(name) ":=" constr(def) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
	let def = Constrintern.interp_constr env evm def in
	let trm = TermReify.denote_term (fst def) in
	let result = Constrextern.extern_constr true env evm (EConstr.of_constr trm) in
	declare_definition name
	  (Decl_kinds.Global, false, Decl_kinds.Definition)
	  [] None result None (Lemmas.mk_hook (fun _ _ -> ())) ]
END;;

VERNAC COMMAND EXTEND Unquote_inductive CLASSIFIED AS SIDEFF
    | [ "Make" "Inductive" constr(def) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
  TermReify.declare_interpret_inductive env evm def ]
END;;

VERNAC COMMAND EXTEND Run_program CLASSIFIED AS SIDEFF
    | [ "Run" "TemplateProgram" constr(def) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
  TermReify.run_template_program env evm def ]
END;;

VERNAC COMMAND EXTEND Make_tests CLASSIFIED AS QUERY
(*
    | [ "Make" "Definitions" tactic(t) ] ->
      [ (** [t] returns a [list (string * term)] **)
	assert false ]
*)
    | [ "Test" "Quote" constr(c) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
	let c = Constrintern.interp_constr env evm c in
	let result = TermReify.quote_term env (fst c) in
(* DEBUGGING
	let back = TermReify.denote_term result in
	Format.eprintf "%a\n" pp_constr result ;
	Format.eprintf "%a\n" pp_constr back ;
	assert (Term.eq_constr c back) ;
*)
        Feedback.msg_notice (Printer.pr_constr result) ;
	() ]
END;;
