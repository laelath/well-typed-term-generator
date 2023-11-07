open Extensions
open Util

(* expression and type datatype *)
type exp_node =
  | Hole of ty * env
  | Ref of var
  | ExtRef of string * ty
  | Let of var * exp * exp
  | Lambda of var list * exp
  | Call of exp * exp list
  | ExtLambda of extvar * var list ref * exp
  | ExtCall of exp * extvar * exp list ref
and exp = exp_node ref
and ty_node =
  | TyCons of string * ty list
  | TyArrow of ty list * ty
  | TyArrowExt of extvar * ty
  | TyUnif of ty
and ty = ty_node UnionFind.elem
and extvar = {
  mutable param_tys : ty list;
  mutable lambdas : var list ref list;
  mutable calls : (exp list ref * env) list;
}
and var = {
  var_name : string;
  var_ty : ty;
  mutable var_refs : exp list;
}
and env = (var list, extvar * var list ref) Either.t list

(* INVARIANTS:
 * - the params list in ExtLambda is contained in the its extvar
 * - the args list in ExtCall is contained in its extvar
 * - the var_refs field in the var of Ref contains itself
 *)

let make_ty : ty_node -> ty  = UnionFind.make
let make_unif () =
  (* knotty crimes *)
  let ty = make_ty (TyCons ("", [])) in
  UnionFind.set ty (TyUnif ty);
  ty

(* Technically variables, like extension variables, don't need a name.
 * But since creating one would be harder as part of an extractor,
 * we do it here.
 *)
let var_counter = ref 0
let reset_var_counter () = var_counter := 0
let new_var ty =
  let x = !var_counter in
  incr var_counter;
  { var_name = "x" ^ Int.to_string x;
    var_ty = ty;
    var_refs = [];
  }

(* TODO: in debug mode check that ref is real *)
(* TODO: special function for creating references *)
let var_register_ref v e =
  v.var_refs <- e :: v.var_refs

(* create a new extension variable *)
let new_extvar () = {
    param_tys = [];
    lambdas = [];
    calls = [];
  }

(* Implements the rule:
   E ~> E{alpha + tau}
 *)
(* extends the extvar with the given type *)
(* returns the list of new holes *)
let extend_extvar ext ty =
  ext.param_tys <- ty :: ext.param_tys;
  List.iter (fun params -> push (new_var ty) params) ext.lambdas;
  List.map (fun (args, env) ->
              let hole = ref (Hole (ty, env)) in
              push hole args;
              hole)
           ext.calls

(* TODO: check well-formedness on registration in debug *)
let extvar_register_lambda ext params =
  ext.lambdas <- params :: ext.lambdas

(* TODO: check well-formedness on registration in debug *)
let extvar_register_call ext args env =
  ext.calls <- (args, env) :: ext.calls

let rec ty_contains_extvar evar ty =
  match UnionFind.get ty with
  | TyCons (_, tys) ->
     List.exists (ty_contains_extvar evar) tys
  | TyArrow (ty_params, ty_body) ->
     List.exists (ty_contains_extvar evar) ty_params ||
     ty_contains_extvar evar ty_body
  | TyArrowExt (evar', ty_body) ->
     evar == evar' || ty_contains_extvar evar ty_body
  | TyUnif _ -> false

(* TODO: shadowing? *)
let filter_env f (env : env) =
  let g x = f x.var_ty in
  List.concat_map
    (Either.fold ~left:(fun l -> List.filter g l)
                 ~right:(fun (_, l) -> List.filter g !l))
    env

(** Unification *)

exception UnificationError

(* not re-entrant on UnionFind.merge because types aren't recursive *)
let rec unify ty10 ty20 =

  (* returns true if if ty_node contains ty' *)
  let contains_ty ty' ty_node0 =
    let rec lp_ty ty =
      UnionFind.eq ty' ty || lp_ty_node (UnionFind.get ty)
    and lp_ty_node ty_node =
      match ty_node with
      | TyCons (_, ty_args) ->
         List.exists lp_ty ty_args
      | TyArrow (ty_args, ty_body) ->
         List.exists lp_ty ty_args || lp_ty ty_body
      | TyArrowExt (evar, ty_body) ->
         List.exists lp_ty evar.param_tys || lp_ty ty_body
      | TyUnif _ -> false in
    lp_ty_node ty_node0 in

  let _ = UnionFind.merge
    (fun ty_node1 ty_node2 ->
      match ty_node1, ty_node2 with
      | TyUnif ty1, _ ->
         if contains_ty ty1 ty_node2
         then raise UnificationError
         else ty_node2
      | _, TyUnif ty2 ->
         if contains_ty ty2 ty_node1
         then raise UnificationError
         else ty_node1
      | TyCons (n1, tys1), TyCons (n2, tys2) ->
         if not (n1 = n2 && List.length tys1 = List.length tys2)
         then raise UnificationError
         else List.iter2 unify tys1 tys2;
              ty_node1
      | TyArrow (ty_args1, ty_body1), TyArrow (ty_args2, ty_body2) ->
         if List.length ty_args1 <> List.length ty_args2
         then raise UnificationError
         else List.iter2 unify ty_args1 ty_args2;
              unify ty_body1 ty_body2;
              ty_node1
      | TyArrowExt (evar1, ty_body1), TyArrowExt (evar2, ty_body2) ->
         if evar1 != evar2
         then raise UnificationError
         else unify ty_body1 ty_body2;
              ty_node1
      | _, _ -> raise UnificationError)
    ty10 ty20 in ()

(* feels kinda wasteful that the mapping is just thrown away,
   but I suspect that the benefits of fully unifying the types
   might outweigh it? *)
(* TODO: could merge unification variable free types here
         for faster repeat checking, kinda hacky though *)
let can_unify ty10 ty20 =

  let lookup ty mp0 =
    let ty_rep = UnionFind.find ty in
    let rec lp mp =
      match mp with
      | [] -> None
      | (ty_rep', ty') :: mp' ->
         if ty_rep == ty_rep'
         then Some (ty', mp')
         else lp mp' in
    lp mp0 in

  let add ty ty' mp = (UnionFind.find ty, ty') :: mp in

  (* returns true if if ty_node contains ty' *)
  let contains_ty mp0 ty' ty_node0 =
    let rec lp_ty mp ty =
      UnionFind.eq ty' ty || lp_ty_node mp (UnionFind.get ty)
    and lp_ty_node mp ty_node =
      match ty_node with
      | TyCons (_, ty_args) ->
         List.exists (lp_ty mp) ty_args
      | TyArrow (ty_args, ty_body) ->
         List.exists (lp_ty mp) ty_args || lp_ty mp ty_body
      | TyArrowExt (evar, ty_body) ->
         List.exists (lp_ty mp) evar.param_tys || lp_ty mp ty_body
      | TyUnif ty ->
         match lookup ty mp with
         | None -> false
         | Some (ty1, mp') -> lp_ty mp' ty1 in
    lp_ty_node mp0 ty_node0 in

  let rec lp mp ty1 ty2 =
    if UnionFind.eq ty1 ty2 then mp else
    match UnionFind.get ty1, UnionFind.get ty2 with
    | TyUnif _, ty_node2 ->
       (match lookup ty1 mp with
        | Some (ty1', _) -> lp mp ty1' ty2
        | None ->
           if contains_ty mp ty1 ty_node2
           then raise UnificationError
           else add ty1 ty2 mp)
    | ty_node1, TyUnif _ ->
       (match lookup ty2 mp with
        | Some (ty2', _) -> lp mp ty1 ty2'
        | None ->
           if contains_ty mp ty2 ty_node1
           then raise UnificationError
           else add ty2 ty1 mp)
    | TyCons (n1, tys1), TyCons (n2, tys2) ->
       if not (n1 = n2 && List.length tys1 = List.length tys2)
       then raise UnificationError
       else List.fold_left2 lp mp tys1 tys2
    | TyArrow (ty_args1, ty_body1), TyArrow (ty_args2, ty_body2) ->
       if List.length ty_args1 <> List.length ty_args2
       then raise UnificationError
       else lp (List.fold_left2 lp mp ty_args1 ty_args2)
               ty_body1 ty_body2
    | TyArrowExt (evar1, ty_body1), TyArrowExt (evar2, ty_body2) ->
       if evar1 != evar2
       then raise UnificationError
       else lp mp ty_body1 ty_body2
    | _, _ -> raise UnificationError
  in
  try
    let _ = lp [] ty10 ty20 in
    true
  with
    UnificationError -> false

let ty_is_fun_producing ty ty_f =
  match UnionFind.get ty_f with
  | TyArrow (_, ty_body) -> can_unify ty ty_body
  | TyArrowExt (_, ty_body) -> can_unify ty ty_body 
  | _ -> false


(** Converting between internal and external facing types *)

(* dictionary of zero-arg type constructors *)
let ty_dict = ref SM.empty
let ty_of_external_ty (ty_top : External.ty) =
  let vars_map =
    SM.of_string_set (fun _ -> make_unif ()) (External.ty_vars ty_top) in
  let rec lp (ty : External.ty) =
    match ty with
    | TyCons (name, ty_args) ->
       (match ty_args with
        | [] ->
           (match SM.find_opt name !ty_dict with
            | Some ty_ref -> ty_ref
            | None ->
               let ty_ref = make_ty (TyCons (name, [])) in
               ty_dict := SM.add name ty_ref !ty_dict;
               ty_ref)
        | _ -> make_ty (TyCons (name, List.map lp ty_args)))
    | TyFun (arg_tys, ty_body) ->
       make_ty (TyArrow (List.map lp arg_tys, lp ty_body))
    | TyVar a -> SM.find a vars_map in
  lp ty_top


(* uty is used in place of any unresolved unification variables *)
let ty_to_external_ty uty ty0 : External.ty =
  let[@tail_mod_cons] rec lp ty =
    match UnionFind.get ty with
    | TyUnif _ -> uty
    | TyCons (name, tys) ->
       External.TyCons (name, List.map lp tys)
    | TyArrow (ty_args, ty_body) ->
       External.TyFun (List.map lp ty_args, lp ty_body)
    | TyArrowExt (evar, ty_body) ->
       lp (make_ty (TyArrow (evar.param_tys, ty_body))) in
  lp ty0

exception FoundHole

let exp_to_external_exp uty e0 =
  let[@tail_mod_cons] rec lp env e =
    match !e with
    | Hole _ -> raise FoundHole
    | Ref x -> List.assq x env
    | ExtRef (x, ty) -> External.Ref (x, ty_to_external_ty uty ty)
    | Let (x, e1, e2) ->
       let x_ty = ty_to_external_ty uty x.var_ty in
       External.Let
         ((x.var_name, x_ty), lp env e1,
          (lp[@tailcall])
            ((x, External.Ref (x.var_name, x_ty)) :: env)
            e2)
    | Lambda (xs, e_body) ->
       let xs_tys = List.map (fun x ->
                               ty_to_external_ty uty x.var_ty)
                             xs in
       External.Lambda
         (List.map2 (fun x ty -> (x.var_name, ty)) xs xs_tys,
          lp (List.map2 (fun x ty ->
                           (x, External.Ref (x.var_name, ty)))
                        xs xs_tys @ env)
             e_body)
    | Call (e_f, e_args) ->
       External.Call
         (lp env e_f,
          List.map (lp env) e_args)
    | ExtLambda (_, xs, e_body) ->
       lp env (ref (Lambda (!xs, e_body)))
    | ExtCall (e_f, _, e_args) ->
       lp env (ref (Call (e_f, !e_args))) in
  lp [] e0


(** Debug mode invariant checking functions *)

exception ConsistencyError of string

let ensure_same_env (env1 : env) (env2 : env) =
  if List.equal
       (Either.equal
          ~left:(List.equal (==))
          ~right:(fun (ev1, lr1) (ev2, lr2) ->
                    ev1 == ev2 && lr1 == lr2))
       env1 env2
  then ()
  else raise (ConsistencyError "different environments")

(* TODO: shadowing? *)
let ensure_var_in_env (x : var) (env : env) =
  if List.exists (Either.fold ~left:(List.memq x)
                              ~right:(fun (_, l) -> List.memq x !l))
                 env
  then ()
  else raise (ConsistencyError "var not bound in env")

let rec consistency_check_ty ty =
  match UnionFind.get ty with
  | TyUnif ty' ->
     if UnionFind.eq ty ty'
     then ()
     else raise (ConsistencyError "unif var ill-formed");
  | TyCons (_, tys) -> List.iter consistency_check_ty tys
  | TyArrow (ty_args, ty_body) ->
     List.iter consistency_check_ty ty_args;
     consistency_check_ty ty_body
  | TyArrowExt (evar, ty_body) ->
     List.iter consistency_check_ty evar.param_tys;
     consistency_check_ty ty_body

let rec consistency_check env e =
  match !e with
  | Hole (ty, env') ->
     ensure_same_env env env';
     consistency_check_ty ty
  | Ref x ->
     if not (List.memq e x.var_refs)
     then raise (ConsistencyError "var ref not in refs list");
     ensure_var_in_env x env
  | ExtRef (_, ty) ->
     consistency_check_ty ty
  | Let (x, e1, e2) ->
     consistency_check_ty x.var_ty;
     consistency_check env e1;
     consistency_check (Either.Left [x] :: env) e2
  | Lambda (xs, e_body) ->
     List.iter (fun x -> consistency_check_ty x.var_ty) xs;
     consistency_check (Either.Left xs :: env) e_body
  | Call (e_f, e_args) ->
     consistency_check env e_f;
     List.iter (consistency_check env) e_args
  | ExtLambda (evar, params, e_body) ->
     if not (List.memq params evar.lambdas)
     then raise (ConsistencyError "ext. lambda params not in extvar");
     List.iter (fun x -> consistency_check_ty x.var_ty) !params;
     consistency_check (Either.Right (evar, params) :: env) e_body
  | ExtCall (e_f, evar, e_args) ->
     (match List.assq_opt e_args evar.calls with
      | None -> raise (ConsistencyError "ext. call args not in extvar")
      | Some env' -> ensure_same_env env env');
     consistency_check env e_f;
     List.iter (consistency_check env) !e_args

exception TypeCheckError of string

(* not re-entrant on UnionFind.merge because types aren't recursive *)
let rec ensure_same_ty ty1 ty2 =
  let _ = UnionFind.merge
    (fun ty_node1 ty_node2 ->
      match ty_node1, ty_node2 with
      | TyCons (name1, ty_args1), TyCons (name2, ty_args2) ->
         if name1 <> name2
         then raise (TypeCheckError "different type cons names");
         if List.length ty_args1 <> List.length ty_args2
         then raise (TypeCheckError "different number of type cons args");
         List.iter2 ensure_same_ty ty_args1 ty_args2;
         ty_node1
      | TyArrow (ty_args1, ty_body1), TyArrow (ty_args2, ty_body2) ->
         if List.length ty_args1 <> List.length ty_args2
         then raise (TypeCheckError "different number of fun args");
         List.iter2 ensure_same_ty ty_args2 ty_args2;
         ensure_same_ty ty_body1 ty_body2;
         ty_node1
      | TyArrowExt (extvar1, ty_body1), TyArrowExt (extvar2, ty_body2) ->
         if extvar1 != extvar2
         then raise (TypeCheckError "different extvars");
         ensure_same_ty ty_body1 ty_body2;
         ty_node1
      | TyUnif _, TyUnif _ ->
         raise (TypeCheckError "different unification variables")
      | _, _ -> raise (TypeCheckError "different type constructors"))
    ty1 ty2 in ()

(* typecheck *)
let typecheck ext_refs (e : exp) =
  let rec lp (e : exp) =
    match !e with
    | Hole (ty, _) -> ty
    | Ref x -> x.var_ty
    | ExtRef (x, ty) ->
       (match List.assoc_opt x ext_refs with
        | None -> raise (TypeCheckError "external ref not bound")
        | Some ext_ty ->
          if not (can_unify ty (ty_of_external_ty ext_ty))
          then raise (TypeCheckError "external ref has invalid type");
          ty)
    | Let (x, e1, e2) ->
       ensure_same_ty (lp e1) x.var_ty;
       lp e2
    | Lambda (xs, e_body) ->
       make_ty (TyArrow (List.map (fun x -> x.var_ty) xs, lp e_body))
    | Call (e_f, e_args) ->
       let ty_f = lp e_f in
       (match UnionFind.get ty_f with
        | TyArrow (ty_args, ty_body) ->
           if List.length ty_args <> List.length e_args
           then raise (TypeCheckError "different call args length");
           List.iter2 (fun e_arg ty_arg ->
                         ensure_same_ty (lp e_arg) ty_arg)
                      e_args ty_args;
           ty_body
        | _ -> raise (TypeCheckError "call of non-function"))
    | ExtLambda (extvar, params, e_body) ->
       if List.length extvar.param_tys <> List.length !params
       then raise (TypeCheckError "different ext lambda params length");
       List.iter2 (fun x ty -> ensure_same_ty x.var_ty ty)
                  !params extvar.param_tys;
       make_ty (TyArrowExt (extvar, lp e_body))
    | ExtCall (e_f, extvar, e_args) ->
       let ty_f = lp e_f in
       (match UnionFind.get ty_f with
        | TyArrowExt (extvar', ty_body) ->
           if extvar != extvar'
           then raise (TypeCheckError "different extvars");
           if List.length extvar.param_tys <> List.length !e_args
           then raise (TypeCheckError "different ext call args length");
           List.iter2 (fun e_arg ty ->
                         ensure_same_ty (lp e_arg) ty)
                      !e_args extvar.param_tys;
           ty_body
        | _ -> raise (TypeCheckError "ext call of non-ext function"))
  in lp e

type stats = {
  vars              : var list;
  lambda_params     : var list list;
  ext_lambda_params : var list list;
  extvars           : extvar list;
  external_refs     : (string * ty) list;
}

let empty_stats = {
  vars = [];
  lambda_params = [];
  ext_lambda_params = [];
  extvars = [];
  external_refs = [];
}

let merge_stats s1 s2 = {
    vars = s1.vars @ s2.vars;
    lambda_params = s1.lambda_params @ s2.lambda_params;
    ext_lambda_params = s1.ext_lambda_params @ s2.ext_lambda_params;
    extvars = s1.extvars @ s2.extvars;
    external_refs = s1.external_refs @ s2.external_refs;
  }

let memq_add x l =
  if List.memq x l
  then l
  else x :: l

let rec collect_stats e =
  match !e with
  | Hole _ -> empty_stats
  | Ref _ -> empty_stats
  | ExtRef (x, ty) -> { empty_stats with external_refs = [(x, ty)] }
  | Lambda (xs, e_body) ->
     let s = collect_stats e_body in
     { s with lambda_params = xs :: s.lambda_params }
  | Call (e_f, e_args) ->
     List.fold_left (collect_stats -.* merge_stats)
                    (collect_stats e_f) e_args
  | ExtLambda (evar, params, e_body) ->
     let s = collect_stats e_body in
     { s with ext_lambda_params = !params :: s.ext_lambda_params;
              extvars = memq_add evar s.extvars }
  | ExtCall (e_f, evar, e_args) ->
     let s = List.fold_left (collect_stats -.* merge_stats)
                            (collect_stats e_f) !e_args in
     { s with extvars = memq_add evar s.extvars }
  | _ -> raise Unimplemented
