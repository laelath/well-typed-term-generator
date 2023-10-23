(* Each node has a unique label, which cannot be changed.
   if we have some node (call e1_l1 e2_l2) and we are updating e1 to (let (x rhs) e1),
   it's tempting to overwrite the l1 label to point to this new node.
   The problem is that we have update maps `type extension var -> program location set`
   that point to where syntactic updates need to happen, and we don't want to update these.

   Each node also has a `prev` pointer, so there's no term sharing
   allowed; each node has exactly one reference.
 *)

(* expression labels *)
module ExpLabel = Key.Make (struct let x="lab" end)
type exp_label = ExpLabel.t

(* parameter labels for extensible lambdas *)
module ParamsLabel = Key.Make (struct let x="param" end)
type params_label = ParamsLabel.t

(* argument labels for extensible calls *)
module ArgsLabel = Key.Make (struct let x="arg" end)
type args_label = ArgsLabel.t

(* variables *)
module Var = Key.Make (struct let x="x" end)
type var = Var.t

(* expression datatype *)
type exp =
  | Hole
  | Var of var
  | StdLibRef of string
  | Let of (var * exp_label * exp_label)
  | Lambda of ((var list) * exp_label)
  | Call of (exp_label * (exp_label list))
  | ExtLambda of (params_label * exp_label)
  | ExtCall of (exp_label * args_label)
  | ValInt of int
  | ValBool of bool
  | Cons of (exp_label * exp_label)
  | Empty
  | Match of (exp_label * exp_label * (var * var * exp_label))
  | If of (exp_label * exp_label * exp_label)
  | Custom of string
(*
  | Data of {
      dcon : Data.dcon;
      args : exp_label list;
    }
  | Match of {
      arg : exp_label;
      pats : pat list;
    }
and pat = {
    dcon : Data.dcon;
    params : var list;
    body : exp_label;
  }
*)
(* | Prim of prim * label list *)

(* expression nodes *)
type exp_node = {
    exp : exp;
    ty : Type.ty_label;
    prev : exp_label option;
  }

type program = {
    (* the head node of the program *)
    mutable head : exp_label;

    std_lib : (string * Type.flat_ty) list;

    (* variable operations *)
    new_var : unit -> var;
    (* extension variable operations *)
    new_extvar : unit -> Type.extvar;

    ty : Type.registry;
    (*
    (* type operations *)
    new_ty : Type.ty -> Type.ty_label;
    get_ty : Type.ty_label -> Type.ty;
     *)
    (*
    (* type parameter operations *)
    new_ty_params : Type.extvar -> Type.ty_params_label;
    get_ty_params : Type.ty_params_label -> Type.ty_label list;
    add_ty_param : Type.ty_params_label -> Type.ty_label -> unit;
    (* all params labels that are associated with the given extvar *)
    extvar_ty_params : Type.extvar -> Type.ty_params_label list;
    ty_params_extvar : Type.ty_params_label -> Type.extvar;
     *)

    (* expression operations *)
    new_exp : exp_node -> exp_label;
    get_exp : exp_label -> exp_node;
    set_exp : exp_label -> exp_node -> unit;

    (* lambda parameter operations *)
    new_params : Type.extvar -> params_label;
    get_params : params_label -> var list;
    add_param : params_label -> var -> unit;
    (* all params labels that are associated with the given extvar *)
    extvar_params : Type.extvar -> params_label list;
    params_extvar : params_label -> Type.extvar;

    (* arguments operations *)
    new_args : Type.extvar -> exp_label -> args_label;
    get_args : args_label -> exp_label list;
    add_arg : args_label -> exp_label -> unit;
    (* the node that contains this args label *)
    args_parent : args_label -> exp_label;
    (* all args labels that are associated with the given extvar *)
    extvar_args : Type.extvar -> args_label list;
    args_extvar : args_label -> Type.extvar;

    (* FIXME *)
    rename_child : (exp_label * exp_label) -> exp_label -> unit;
  }

let make_program ?(std_lib = []) ty =
  let exp_tbl : exp_node ExpLabel.Tbl.t = ExpLabel.Tbl.create 100 in
  let params_tbl : (var list) ParamsLabel.Tbl.t = ParamsLabel.Tbl.create 100 in
  let args_tbl : (exp_label list) ArgsLabel.Tbl.t = ArgsLabel.Tbl.create 100 in
  let extvar_params_tbl : (params_label list) Type.ExtVar.Tbl.t = Type.ExtVar.Tbl.create 100 in
  let extvar_args_tbl : (args_label list) Type.ExtVar.Tbl.t = Type.ExtVar.Tbl.create 100 in
  let args_parent_tbl : exp_label ArgsLabel.Tbl.t = ArgsLabel.Tbl.create 100 in
  let params_extvar_tbl : Type.extvar ParamsLabel.Tbl.t = ParamsLabel.Tbl.create 100 in
  let args_extvar_tbl : Type.extvar ArgsLabel.Tbl.t = ArgsLabel.Tbl.create 100 in

  let ty_registry = Type.make () in

  let new_var () = Var.make() in
  let new_extvar () =
    let extvar = ty_registry.new_extvar () in
    Type.ExtVar.Tbl.add extvar_params_tbl extvar [];
    Type.ExtVar.Tbl.add extvar_args_tbl extvar [];
    extvar in


  let new_exp node =
    let lab = ExpLabel.make() in
    ExpLabel.Tbl.add exp_tbl lab node;
    lab in
  let get_exp lab = ExpLabel.Tbl.find exp_tbl lab in
  let set_exp lab node = ExpLabel.Tbl.replace exp_tbl lab node in

  let new_params extvar =
    let lab = ParamsLabel.make() in
    ParamsLabel.Tbl.add params_tbl lab [];
    Type.ExtVar.Tbl.replace extvar_params_tbl extvar
                       (lab :: (Type.ExtVar.Tbl.find extvar_params_tbl extvar));
    ParamsLabel.Tbl.add params_extvar_tbl lab extvar;
    lab in
  let get_params lab = ParamsLabel.Tbl.find params_tbl lab in
  let add_param lab var =
    ParamsLabel.Tbl.replace params_tbl lab
                            (var :: (ParamsLabel.Tbl.find params_tbl lab));
    () in
  let extvar_params extvar = Type.ExtVar.Tbl.find extvar_params_tbl extvar in
  let params_extvar lab = ParamsLabel.Tbl.find params_extvar_tbl lab in


  let new_args extvar parent =
    let lab = ArgsLabel.make() in
    ArgsLabel.Tbl.add args_tbl lab [];
    Type.ExtVar.Tbl.replace extvar_args_tbl extvar
                       (lab :: (Type.ExtVar.Tbl.find extvar_args_tbl extvar));
    ArgsLabel.Tbl.add args_extvar_tbl lab extvar;
    ArgsLabel.Tbl.add args_parent_tbl lab parent;
    lab in
  let get_args lab = ArgsLabel.Tbl.find args_tbl lab in
  let add_arg lab node =
    ArgsLabel.Tbl.replace args_tbl lab
                          (node :: (ArgsLabel.Tbl.find args_tbl lab));
    () in
  let extvar_args extvar = Type.ExtVar.Tbl.find extvar_args_tbl extvar in
  let args_extvar lab = ArgsLabel.Tbl.find args_extvar_tbl lab in
  let args_parent lab = ArgsLabel.Tbl.find args_parent_tbl lab in

  (* Justin: I hate this so much *)
  (* Ben: a necessary evil *)
  let rename_child (a, b) e =
    let rename e' = if e' == a then b else e' in

    let node = get_exp e in
    let set e' = set_exp e {exp=e'; ty=node.ty; prev=node.prev} in
    match node.exp with
    | Let (x, rhs, body) ->
       set (Let (x, rename rhs, rename body))
    | Lambda (params, body) ->
      set (Lambda (params, rename body))
    | Call (func, args) ->
      set (Call (rename func, (List.map rename args)))
    | ExtLambda (params, body) ->
      set (ExtLambda (params, rename body))
    | ExtCall (func, args) ->
      ArgsLabel.Tbl.replace args_tbl args (List.map rename (get_args args));
      set (ExtCall (rename func, args))
    | If (pred, thn, els) ->
      set (If (rename pred, rename thn, rename els))
    | Cons (fst, rst) ->
      set (Cons (rename fst, rename rst))
    | Match (scr, nil, (fst, rst, cons)) ->
       set (Match (rename scr, rename nil, (fst, rst, rename cons)))
    | _ -> () in

  let head = new_exp {exp=Hole; ty=ty_registry.flat_ty_to_ty ty; prev=None} in

  {
    head = head;

    std_lib = std_lib;

    ty = ty_registry;
    new_var = new_var;
    new_extvar = new_extvar;

    new_exp = new_exp;
    get_exp = get_exp;
    set_exp = set_exp;

    new_params = new_params;
    get_params = get_params;
    add_param = add_param;
    extvar_params = extvar_params;
    params_extvar = params_extvar;

    new_args = new_args;
    get_args = get_args;
    add_arg = add_arg;
    args_parent = args_parent;
    extvar_args = extvar_args;
    args_extvar = args_extvar;

    rename_child = rename_child;
  }

(* check that the prev pointers are correct,
   and that each node points to itself *)
let consistency_check prog =

  let rec check prev e =
    let node = prog.get_exp e in
    if prev <> node.prev
    then raise (Util.ConsistencyError "Previous node pointer mismatch")
    else Type.consistency_check prog.ty node.ty;
         match node.exp with
         | Hole -> ()
         | Var _ -> ()
         | StdLibRef _ -> ()

         | ValInt _ -> ()
         | ValBool _ -> ()

         | Empty -> ()
         | Cons (e1, e2) -> check (Some e) e1; check (Some e) e2
         | Match (e1, e2, (_, _, e3)) -> check (Some e) e1; check (Some e) e2; check (Some e) e3

         | Let (_, rhs, body) -> check (Some e) rhs; check (Some e) body
         | Lambda (_, body) -> check (Some e) body
         | Call (func, args) -> List.iter (check (Some e)) args; check (Some e) func

         | ExtLambda (params, body) ->
           let extvar = prog.params_extvar params in
           if not (List.mem params (prog.extvar_params extvar))
           then raise (Util.ConsistencyError "params label not in extvar list")
           else check (Some e) body

         | ExtCall (func, args) ->
           let extvar = prog.args_extvar args in
           if not (List.mem args (prog.extvar_args extvar))
           then raise (Util.ConsistencyError "args label not in extvar list")
           else List.iter (check (Some e)) (prog.get_args args);
                check (Some e) func

         | If (pred, thn, els) -> check (Some e) pred; check (Some e) thn; check (Some e) els

(*
         | Data {dcon=_; args=_} -> () (* todo *)
         | Match {arg=_; pats=_} -> () (* todo *)
*)
         | Custom _ -> ()
    in
  (* check that the argsvars points to params, ty_params, and args *)
  check None prog.head


exception TypeCheckError of string

(* type check *)
let type_check (prog : program) =
  (* TODO: better errors *)

  let ensure_same_extvar ex1 ex2 =
    if Type.ExtVar.equal ex1 ex2
    then ()
    else raise (TypeCheckError "extvar mismatch") in

  let ensure_same_ty tyl1 tyl2 =
    if Type.is_same_ty prog.ty tyl1 tyl2
    then ()
    else raise (TypeCheckError "Type mismatch") in

  let ensure_ty_compat ty tyl =
    match Type.ty_compat_ty_label prog.ty ty tyl [] with
    | None -> print_string (Type.string_of prog.ty tyl);
              print_newline ();
              raise (TypeCheckError "Invalid stdlib reference")
    | Some _ -> () in

  let rec type_check_exp gamma e =

    let rec type_check_args exps tys =
      (match (exps, tys) with
       | ([], []) -> ()
       | (exp :: exps', ty :: tys') ->
         let ty' = type_check_exp gamma exp in
         ensure_same_ty ty ty';
         type_check_args exps' tys'
       | _ -> raise (TypeCheckError "number of function call args differs from type")) in

    let node = prog.get_exp e in
    match node.exp with
    | Hole -> node.ty
    | Var var ->
      (match List.assoc_opt var gamma with
       | None -> raise (TypeCheckError "Variable not in scope")
       | Some ty' -> ensure_same_ty node.ty ty'; node.ty)
    | StdLibRef str ->
      (match List.assoc_opt str prog.std_lib with
       | None -> raise (TypeCheckError "std lib object not found")
       | Some ty' -> ensure_ty_compat ty' node.ty; node.ty)

    | ValInt _ ->
      if (prog.ty.get_ty node.ty) == TyInt
      then node.ty
      else raise (TypeCheckError "ValInt doesn't have type TyInt")

    | Empty ->
      (match (prog.ty.get_ty node.ty) with
       | TyList _ -> node.ty
       | _ -> raise (TypeCheckError "Empty doesn't have list type"))

    | Cons (e1, e2) ->
      let ty1 = type_check_exp gamma e1 in
      let ty2 = type_check_exp gamma e2 in
      (match prog.ty.get_ty ty2 with
       | TyList ty2' -> ensure_same_ty ty1 ty2'
       | _ -> raise (TypeCheckError "Cons doesn't have a list type"));
      node.ty

    | Match (e1, e2, (x, y, e3)) ->
      let ty1 = type_check_exp gamma e1 in
      let ty1' = (match prog.ty.get_ty ty1 with
                  | TyList ty1' -> ty1'
                  | _ -> raise (TypeCheckError "Match scrutinee doesn't have list type")) in
      let ty2 = type_check_exp gamma e2 in
      let ty3 = type_check_exp ((x, ty1') :: (y, ty1) :: gamma) e3 in
      ensure_same_ty ty2 ty3;
      node.ty

    | ValBool _ ->
      if (prog.ty.get_ty node.ty) == TyBool
      then node.ty
      else raise (TypeCheckError "ValBool doesn't have type TyBool")

    | Let (var, rhs, body) ->
      let rhs_ty = type_check_exp gamma rhs in
      let body_ty = type_check_exp ((var, rhs_ty) :: gamma) body in
      ensure_same_ty node.ty body_ty; node.ty

    | Lambda (vars, body) ->
      (match (prog.ty.get_ty node.ty) with
       | TyArrow (tys, ty_im) ->
         let ty_body = type_check_exp ((List.combine vars tys) @ gamma) body in
         ensure_same_ty ty_body ty_im;
         node.ty
       | _ -> raise (TypeCheckError "lambda exp type not (closed) function type"))

    | Call (func, args) ->
      let func_ty = type_check_exp gamma func in
      (match (prog.ty.get_ty func_ty) with
       | TyArrow (tys, ty_im) ->
         ensure_same_ty node.ty ty_im;
         type_check_args args tys;
         node.ty
       | _ -> raise (TypeCheckError "callee exp not (closed) function type"))

    (* todo: check and raise custom error when arg names and types
             have different lengths *)
    | ExtLambda (params, body) ->
      (match (prog.ty.get_ty node.ty) with
       | TyArrowExt (ty_params, ty_im) ->
         ensure_same_extvar (prog.params_extvar params) (prog.ty.ty_params_extvar ty_params);
         let vars = prog.get_params params in
         let tys = prog.ty.get_ty_params ty_params in
         let ty_body = type_check_exp ((List.combine vars tys) @ gamma) body in
         ensure_same_ty ty_body ty_im;
         node.ty
       | _ -> raise (TypeCheckError "lambda exp type not (ext) function type"))

    | ExtCall (func, args) ->
      let func_ty = type_check_exp gamma func in
      (match (prog.ty.get_ty func_ty) with
       | TyArrowExt (ty_params, ty_im) ->
         ensure_same_extvar (prog.args_extvar args) (prog.ty.ty_params_extvar ty_params);
         ensure_same_ty node.ty ty_im;
         let exps = prog.get_args args in
         let tys = prog.ty.get_ty_params ty_params in
         type_check_args exps tys;
         node.ty
       | _ -> raise (TypeCheckError "callee exp not (ext) function type"))

    | If (pred, thn, els) ->
      let typ = prog.ty.get_ty (type_check_exp gamma pred) in
      if typ == TyBool
      then (ensure_same_ty node.ty (type_check_exp gamma thn);
            ensure_same_ty node.ty (type_check_exp gamma els);
            node.ty)
      else raise (TypeCheckError "if predicate does not have boolean type")

(*
    | Data {dcon=_; args=_} -> ty (* todo *)

    | Match {arg=arg; pats=_} ->
      let _ = typeCheckExp gamma arg in
      ty
      (* todo: check that arg has the right data type*)
      (* todo: want a totality check? *)
      (* todo: i have no idea what is going on with dcons at all *)
      (* todo: wtaf am i supposed to do here *)
*)
    | Custom _ -> node.ty
  in
  (* throw away the type label *)
  let _ = type_check_exp [] prog.head in
  ()

(* perform the checks *)
let check prog = (
    consistency_check prog;
    type_check prog;
    ()
  )

(*
let count_binds (prog : program) =
  let rec exp_binds (e_lbl : exp_label) =
    let node = prog.get_exp e_lbl in
    match node.exp with
    | Hole -> 0
    | Var _ -> 0
    | StdLibRef _ -> 0
    | Let (_, rhs, body) -> 1 + exp_binds rhs + exp_binds body
    | Lambda (vars, body) -> List.length vars + exp_binds body
    | Call (f, args) -> List.fold_left (+) (exp_binds f) (List.map exp_binds args)
    | ExtLambda (params_lbl, body) ->
      let vars = prog.get_params params_lbl in
      List.length vars + exp_binds body
    | ExtCall (f, args_lbl) ->
      let args = prog.get_args args_lbl in
      List.fold_left (+) (exp_binds f) (List.map exp_binds args)
    | ValInt _ -> 0
    | ValBool _ -> 0
    | Cons (e1, e2) -> exp_binds e1 + exp_binds e2
    | Empty -> 0
    | Match (e1, e2, (_, _, e3)) -> 2 + exp_binds e1 + exp_binds e2 + exp_binds e3
    | If (pred, thn, els) -> exp_binds pred + exp_binds thn + exp_binds els
    | Custom _ -> 0
    in
  exp_binds prog.head
*)

let count_let = false
let count_lambda = false
let count_ext_lambda = false
let count_match = true

let count_binds (prog : program) =
  let sum = List.fold_left (+) 0 in
  let base = (Util.SS.empty, (0, 0)) in
  let num_unbound free = List.fold_left (fun n x -> if Util.SS.mem (Var.to_string x) free then n else n + 1) 0 in
  let remove_vars = List.fold_left (fun free x -> Util.SS.remove (Var.to_string x) free) in
  let rec exp_binds (e_lbl : exp_label) : (Util.SS.t * (int * int)) =
    let node = prog.get_exp e_lbl in
    match node.exp with
    | Hole -> base
    | Var x -> (Util.SS.singleton (Var.to_string x), (0, 0))
    | StdLibRef _ -> base
    | Let (x, rhs, body) ->
      let (free_rhs, (t_rhs, u_rhs)) = exp_binds rhs in
      let (free_body, (t_body, u_body)) = exp_binds body in
      (Util.SS.union free_rhs (remove_vars free_body [x]),
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
      (List.fold_left Util.SS.union free_f frees_args,
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
      (List.fold_left Util.SS.union free_f frees_args,
       (sum ts_args + t_f, sum us_args + u_f))
    | ValInt _ -> base
    | ValBool _ -> base
    | Cons (e1, e2) ->
      let (free_e1, (t_e1, u_e1)) = exp_binds e1 in
      let (free_e2, (t_e2, u_e2)) = exp_binds e2 in
      (Util.SS.union free_e1 free_e2, (t_e1 + t_e2, u_e1 + u_e2))
    | Empty -> base
    | Match (e1, e2, (x, y, e3)) ->
      let (free_e1, (t_e1, u_e1)) = exp_binds e1 in
      let (free_e2, (t_e2, u_e2)) = exp_binds e2 in
      let (free_e3, (t_e3, u_e3)) = exp_binds e3 in
      (Util.SS.union free_e1 (Util.SS.union free_e2 (remove_vars free_e3 [x; y])),
       (t_e1 + t_e2 + t_e3 + (if count_match then 2 else 0),
        u_e1 + u_e2 + u_e3 + (if count_match then num_unbound free_e3 [x; y] else 0)))
    | If (pred, thn, els) ->
      let (free_pred, (t_pred, u_pred)) = exp_binds pred in
      let (free_thn, (t_thn, u_thn)) = exp_binds thn in
      let (free_els, (t_els, u_els)) = exp_binds els in
      (Util.SS.union free_pred (Util.SS.union free_thn free_els),
       (t_pred + t_thn + t_els, u_pred + u_thn + u_els))
    | Custom _ -> base
    in
  snd (exp_binds prog.head)
