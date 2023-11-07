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

(* technically variables, like extension variables don't need a name
 * but since creating one would be harder as part of an extractor,
 * we do it here
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

(* TODO: check well-formedness on registration *)
let extvar_register_lambda ext params =
  ext.lambdas <- params :: ext.lambdas

(* TODO: check well-formedness on registration *)
let extvar_register_call ext args env =
  ext.calls <- (args, env) :: ext.calls

(* returns true if if ty contains ty' *)
(* TODO: less confusing name *)
let rec ty_contains_ty ty' ty =
  UnionFind.eq ty' ty || ty_node_contains_ty ty' (UnionFind.get ty)
and ty_node_contains_ty ty' ty_node =
  match ty_node with
  | TyCons (_, ty_args) ->
     List.exists (ty_contains_ty ty') ty_args
  | TyArrow (ty_args, ty_body) ->
     List.exists (ty_contains_ty ty') ty_args ||
    ty_contains_ty ty' ty_body
  | TyArrowExt (evar, ty_body) ->
     List.exists (ty_contains_ty ty') evar.param_tys ||
     ty_contains_ty ty' ty_body
  | TyUnif _ -> false

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

exception UnificationError

(* not re-entrant on UnionFind.merge because types aren't recursive *)
let rec unify ty10 ty20 =
  let _ = UnionFind.merge
    (fun ty_node1 ty_node2 ->
      match ty_node1, ty_node2 with
      | TyUnif ty1, _ ->
         if ty_node_contains_ty ty1 ty_node2
         then raise UnificationError
         else ty_node2
      | _, TyUnif ty2 ->
         if ty_node_contains_ty ty2 ty_node1
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
(* TODO: FIXME: when checking for circularity, need to recur on unif vars *)
let can_unify ty10 ty20 =
  let rec lp mp ty1 ty2 =
    if UnionFind.eq ty1 ty2 then mp else
    match UnionFind.get ty1, UnionFind.get ty2 with
    | TyUnif _, ty_node2 ->
       (match List.assq_opt (UnionFind.find ty1) mp with
        | Some ty1' -> lp mp ty1' ty2
        | None ->
           if ty_node_contains_ty ty1 ty_node2
           then raise UnificationError
           else (UnionFind.find ty1, ty2) :: mp)
    | ty_node1, TyUnif _ ->
       (match List.assq_opt (UnionFind.find ty2) mp with
        | Some ty2' -> lp mp ty1 ty2'
        | None ->
           if ty_node_contains_ty ty2 ty_node1
           then raise UnificationError
           else (UnionFind.find ty2, ty1) :: mp)
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

(*
let make_program ?(ext_refs = []) (ty : External.ty) =
  if not (SS.is_empty (External.ty_vars ty))
  then raise (Invalid_argument "supplied type contains type variables");
  let prog_ty = ty_of_external_ty ty in
  let init_hole =
    ref (Hole { hole_ty = prog_ty;
                hole_vars = [];
                hole_params = [];
              }) in
  {
    head = init_hole;
    holes = [init_hole];
    ext_refs = ext_refs;
  }
*)

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

(* TODO: shadowing *)
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
  | ExtRef _ -> ()
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
         if extvar1 <> extvar2
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

exception FoundHole

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


type binding_stats = {
  n_vars                  : int;
  n_let_vars              : int;
  n_lambda_vars           : int;
  n_ext_lambda_vars       : int;
  n_bound_vars            : int;
  n_bound_let_vars        : int;
  n_bound_lambda_vars     : int;
  n_bound_ext_lambda_vars : int;
}

(*
type count_flags = bool * bool * bool * bool

let flag_count_lambda = (false, true, false, false)
let flag_count_ext_lambda = (false, false, true, false)
let flag_count_let = (true, false, false, false)

let count_binds (flags : count_flags) (prog : program) =
  let (count_let, count_lambda, count_ext_lambda, count_match) = flags in
  let sum = List.fold_left (+) 0 in
  let base = (SS.empty, (0, 0)) in
  let num_unbound free = List.fold_left (fun n x -> if SS.mem (Var.to_string x) free then n else n + 1) 0 in
  let remove_vars = List.fold_left (fun free x -> SS.remove (Var.to_string x) free) in
  let rec exp_binds (e_lbl : exp_label) : (SS.t * (int * int)) =
    let node = prog.get_exp e_lbl in
    match node.exp with
    | Hole -> base
    | Var x -> (SS.singleton (Var.to_string x), (0, 0))
    | StdLibRef _ -> base
    | Let (x, rhs, body) ->
      let (free_rhs, (t_rhs, u_rhs)) = exp_binds rhs in
      let (free_body, (t_body, u_body)) = exp_binds body in
      (SS.union free_rhs (remove_vars free_body [x]),
       (t_rhs + t_body + (if count_let then 1 else 0),
        u_rhs + u_body + (if count_let then num_unbound free_body [x] else 0)))
    | Lambda (vars, body) ->
      let (free, (t, u)) = exp_binds body in
      (remove_vars free vars,
       (t + (if count_lambda then List.length vars else 0), 
        u + (if count_lambda then num_unbound free vars else 0)))
    | Call (f, args) ->
      let (free_f, (t_f, u_f)) = exp_binds f in
      let (frees_args, tus_args) = List.split (List.map exp_binds args) in
      let (ts_args, us_args) = List.split tus_args in
      (List.fold_left SS.union free_f frees_args,
       (sum ts_args + t_f, sum us_args + u_f))
    | ExtLambda (params_lbl, body) ->
      let vars = prog.get_params params_lbl in
      let (free, (t, u)) = exp_binds body in
      (remove_vars free vars,
       (t + (if count_ext_lambda then List.length vars else 0), 
        u + (if count_ext_lambda then num_unbound free vars else 0)))
    | ExtCall (f, args_lbl) ->
      let args = prog.get_args args_lbl in
      let (free_f, (t_f, u_f)) = exp_binds f in
      let (frees_args, tus_args) = List.split (List.map exp_binds args) in
      let (ts_args, us_args) = List.split tus_args in
      (List.fold_left SS.union free_f frees_args,
       (sum ts_args + t_f, sum us_args + u_f))
    | ValInt _ -> base
    | ValBool _ -> base
    | Cons (e1, e2) ->
      let (free_e1, (t_e1, u_e1)) = exp_binds e1 in
      let (free_e2, (t_e2, u_e2)) = exp_binds e2 in
      (SS.union free_e1 free_e2, (t_e1 + t_e2, u_e1 + u_e2))
    | Empty -> base
    | Match (e1, e2, (x, y, e3)) ->
      let (free_e1, (t_e1, u_e1)) = exp_binds e1 in
      let (free_e2, (t_e2, u_e2)) = exp_binds e2 in
      let (free_e3, (t_e3, u_e3)) = exp_binds e3 in
      (SS.union free_e1 (SS.union free_e2 (remove_vars free_e3 [x; y])),
       (t_e1 + t_e2 + t_e3 + (if count_match then 2 else 0),
        u_e1 + u_e2 + u_e3 + (if count_match then num_unbound free_e3 [x; y] else 0)))
    | If (pred, thn, els) ->
      let (free_pred, (t_pred, u_pred)) = exp_binds pred in
      let (free_thn, (t_thn, u_thn)) = exp_binds thn in
      let (free_els, (t_els, u_els)) = exp_binds els in
      (SS.union free_pred (SS.union free_thn free_els),
       (t_pred + t_thn + t_els, u_pred + u_thn + u_els))
    | Custom _ -> base
    in
  snd (exp_binds prog.head)
*)
