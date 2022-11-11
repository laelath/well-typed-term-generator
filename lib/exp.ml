
(*
   Types
 *)

(* type labels *)
module TypeLabel = Key.Make (struct let x="ty" end)
type ty_label = TypeLabel.t

(* extension variables *)
module ExtVar = Key.Make (struct let x="ext" end)
type extvar = ExtVar.t

(* type variables for polymorphism *)
(* We don't need these for now
module TyVar = Key.Make (struct let x="a" end)
type ty_var = TyVar.t
 *)

(* type parameter variables for extensible arrow types *)
module TyParamsLabel = Key.Make (struct let x="p" end)
type ty_params_label = TyParamsLabel.t

(* types for data pointers *)
module DataTy = Key.Make (struct let x="d" end)

(* type datatype *)
type ty_node = (* TyArrow of ty_label list * ty_label *)
  | TyNdInt
  | TyNdBool
  | TyNdList of ty_label
  | TyNdArrow of (ty_label list) * ty_label
  | TyNdArrowExt of ty_params_label * ty_label
  (* | TyVar of ty_var *)
(*type ty_node = {ty : ty}*)

(* type tree datatype *)
type ty =
  | TyInt
  | TyBool
  | TyList of ty
  | TyArrow of (ty list) * ty
  | TyVar of string

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
    ty : ty_label;
    prev : exp_label option;
  }

type program = {
    (* the head node of the program *)
    mutable head : exp_label;

    std_lib : (string * (ty * int)) list;

    (* variable operations *)
    new_var : unit -> var;
    (* extension variable operations *)
    new_extvar : unit -> extvar;

    (* type operations *)
    new_ty : ty_node -> ty_label;
    get_ty : ty_label -> ty_node;

    (* expression operations *)
    new_exp : exp_node -> exp_label;
    get_exp : exp_label -> exp_node;
    set_exp : exp_label -> exp_node -> unit;

    (* type parameter operations *)
    new_ty_params : extvar -> ty_params_label;
    get_ty_params : ty_params_label -> ty_label list;
    add_ty_param : ty_params_label -> ty_label -> unit;
    (* all params labels that are associated with the given extvar *)
    extvar_ty_params : extvar -> ty_params_label list;
    ty_params_extvar : ty_params_label -> extvar;

    (* lambda parameter operations *)
    new_params : extvar -> params_label;
    get_params : params_label -> var list;
    add_param : params_label -> var -> unit;
    (* TODO: needed?
    (* the node that contains this params label *)
    (* params_prev : params_label -> exp_label; *)
     *)
    (* all params labels that are associated with the given extvar *)
    extvar_params : extvar -> params_label list;
    params_extvar : params_label -> extvar;

    (* arguments operations *)
    new_args : extvar -> exp_label -> args_label;
    get_args : args_label -> exp_label list;
    add_arg : args_label -> exp_label -> unit;
    (* the node that contains this args label *)
    args_parent : args_label -> exp_label;
    (* all args labels that are associated with the given extvar *)
    extvar_args : extvar -> args_label list;
    args_extvar : args_label -> extvar;

    rename_child : (exp_label * exp_label) -> exp_label -> unit;
  }

exception BadTypeError of string

let make_program ?(std_lib = []) ty =
  let exp_tbl : exp_node ExpLabel.Tbl.t = ExpLabel.Tbl.create 100  in
  let ty_tbl : ty_node TypeLabel.Tbl.t = TypeLabel.Tbl.create 100 in
  let ty_params_tbl : (ty_label list) TyParamsLabel.Tbl.t = TyParamsLabel.Tbl.create 100 in
  let params_tbl : (var list) ParamsLabel.Tbl.t = ParamsLabel.Tbl.create 100 in
  let args_tbl : (exp_label list) ArgsLabel.Tbl.t = ArgsLabel.Tbl.create 100 in
  let extvar_ty_params_tbl : (ty_params_label list) ExtVar.Tbl.t = ExtVar.Tbl.create 100 in
  let extvar_params_tbl : (params_label list) ExtVar.Tbl.t = ExtVar.Tbl.create 100 in
  let extvar_args_tbl : (args_label list) ExtVar.Tbl.t = ExtVar.Tbl.create 100 in
  let args_parent_tbl : exp_label ArgsLabel.Tbl.t = ArgsLabel.Tbl.create 100 in
  let ty_params_extvar_tbl : extvar TyParamsLabel.Tbl.t = TyParamsLabel.Tbl.create 100 in
  let params_extvar_tbl : extvar ParamsLabel.Tbl.t = ParamsLabel.Tbl.create 100 in
  let args_extvar_tbl : extvar ArgsLabel.Tbl.t = ArgsLabel.Tbl.create 100 in

  let new_var () = Var.make() in
  let new_extvar () =
    let extvar = ExtVar.make () in
    ExtVar.Tbl.add extvar_ty_params_tbl extvar [];
    ExtVar.Tbl.add extvar_params_tbl extvar [];
    ExtVar.Tbl.add extvar_args_tbl extvar [];
    extvar in

  let new_ty =
    let bool_lab = TypeLabel.make () in
    TypeLabel.Tbl.add ty_tbl bool_lab TyNdBool;
    let int_lab = TypeLabel.make () in
    TypeLabel.Tbl.add ty_tbl int_lab TyNdInt;
    fun ty' ->
      match ty' with
      | TyNdBool -> bool_lab
      | TyNdInt -> int_lab
      | _ ->
        let lab = TypeLabel.make () in
        TypeLabel.Tbl.add ty_tbl lab ty';
        lab in
  let get_ty lab = TypeLabel.Tbl.find ty_tbl lab in

  let new_exp node =
    let lab = ExpLabel.make() in
    ExpLabel.Tbl.add exp_tbl lab node;
    lab in
  let get_exp lab = ExpLabel.Tbl.find exp_tbl lab in
  let set_exp lab node = ExpLabel.Tbl.replace exp_tbl lab node in

  let new_ty_params extvar =
    let lab = TyParamsLabel.make() in
    TyParamsLabel.Tbl.add ty_params_tbl lab [];
    ExtVar.Tbl.replace extvar_ty_params_tbl extvar
                       (lab :: (ExtVar.Tbl.find extvar_ty_params_tbl extvar));
    TyParamsLabel.Tbl.add ty_params_extvar_tbl lab extvar;
    lab in
  let get_ty_params lab = TyParamsLabel.Tbl.find ty_params_tbl lab in
  let add_ty_param lab ty =
    TyParamsLabel.Tbl.replace ty_params_tbl lab
                              (ty :: (TyParamsLabel.Tbl.find ty_params_tbl lab));
    () in
  let extvar_ty_params extvar = ExtVar.Tbl.find extvar_ty_params_tbl extvar in
  let ty_params_extvar lab = TyParamsLabel.Tbl.find ty_params_extvar_tbl lab in

  let new_params extvar =
    let lab = ParamsLabel.make() in
    ParamsLabel.Tbl.add params_tbl lab [];
    ExtVar.Tbl.replace extvar_params_tbl extvar
                       (lab :: (ExtVar.Tbl.find extvar_params_tbl extvar));
    ParamsLabel.Tbl.add params_extvar_tbl lab extvar;
    lab in
  let get_params lab = ParamsLabel.Tbl.find params_tbl lab in
  let add_param lab var =
    ParamsLabel.Tbl.replace params_tbl lab
                            (var :: (ParamsLabel.Tbl.find params_tbl lab));
    () in
  let extvar_params extvar = ExtVar.Tbl.find extvar_params_tbl extvar in
  let params_extvar lab = ParamsLabel.Tbl.find params_extvar_tbl lab in


  let new_args extvar parent =
    let lab = ArgsLabel.make() in
    ArgsLabel.Tbl.add args_tbl lab [];
    ExtVar.Tbl.replace extvar_args_tbl extvar
                       (lab :: (ExtVar.Tbl.find extvar_args_tbl extvar));
    ArgsLabel.Tbl.add args_extvar_tbl lab extvar;
    ArgsLabel.Tbl.add args_parent_tbl lab parent;
    lab in
  let get_args lab = ArgsLabel.Tbl.find args_tbl lab in
  let add_arg lab node =
    ArgsLabel.Tbl.replace args_tbl lab
                          (node :: (ArgsLabel.Tbl.find args_tbl lab));
    () in
  let extvar_args extvar = ExtVar.Tbl.find extvar_args_tbl extvar in
  let args_extvar lab = ArgsLabel.Tbl.find args_extvar_tbl lab in
  let args_parent lab = ArgsLabel.Tbl.find args_parent_tbl lab in

  (* Justin: I hate this so much *)
  let rename_child (a, b) e =
    let rename e' = if e' == a then b else e' in

    let node = get_exp e in
    match node.exp with
    | Let (x, rhs, body) ->
      set_exp e {exp=Let (x, rename rhs, rename body);
                 ty=node.ty; prev=node.prev}
    | Lambda (params, body) ->
      set_exp e {exp=Lambda (params, rename body);
                 ty=node.ty; prev=node.prev}
    | Call (func, args) ->
      set_exp e {exp=Call (rename func, (List.map rename args));
                 ty=node.ty; prev=node.prev}
    | ExtLambda (params, body) ->
      set_exp e {exp=ExtLambda (params, rename body);
                 ty=node.ty; prev=node.prev}
    | ExtCall (func, args) ->
      ArgsLabel.Tbl.replace args_tbl args (List.map rename (get_args args));
      set_exp e {exp=ExtCall (rename func, args);
                 ty=node.ty; prev=node.prev}
    | If (pred, thn, els) ->
      set_exp e {exp=If (rename pred, rename thn, rename els);
                 ty=node.ty; prev=node.prev}
    | Cons (fst, rst) ->
      set_exp e {exp=Cons (rename fst, rename rst);
                 ty=node.ty; prev=node.prev}
    | Match (scr, nil, (fst, rst, cons)) ->
      set_exp e {exp=Match (rename scr, rename nil, (fst, rst, rename cons));
                 ty=node.ty; prev=node.prev}
    | _ -> () in

  let rec ty_to_ty_label ty' =
    new_ty
      (match ty' with
       | TyInt -> TyNdInt
       | TyBool -> TyNdBool
       | TyList ty'' -> TyNdList (ty_to_ty_label ty'')
       | TyArrow (params, res) -> TyNdArrow (List.rev_map ty_to_ty_label params, ty_to_ty_label res)
       | TyVar _ -> raise (BadTypeError "Cannot generate polymorphic types"))
  in

  let head = new_exp {exp=Hole; ty=ty_to_ty_label ty; prev=None} in

  {
    head = head;

    std_lib = std_lib;

    new_var = new_var;
    new_extvar = new_extvar;
    new_ty = new_ty;
    get_ty = get_ty;

    new_exp = new_exp;
    get_exp = get_exp;
    set_exp = set_exp;

    new_ty_params = new_ty_params;
    get_ty_params = get_ty_params;
    add_ty_param = add_ty_param;
    extvar_ty_params = extvar_ty_params;
    ty_params_extvar = ty_params_extvar;

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

exception ConsistencyError of string

(* check that the prev pointers are correct,
   and that each node points to itself *)
let consistency_check prog =

  let rec consistency_check_ty ty =
    match prog.get_ty ty with
    | TyNdBool -> ()
    | TyNdInt -> ()
    | TyNdList ty' -> consistency_check_ty ty'
    | TyNdArrow (params, ty_im) ->
      List.iter consistency_check_ty params;
      consistency_check_ty ty_im
    | TyNdArrowExt (ty_params, ty_im) ->
      let extvar = prog.ty_params_extvar ty_params in
      if not (List.mem ty_params (prog.extvar_ty_params extvar))
      then raise (ConsistencyError "ty_params label not in extvar list")
      else List.iter consistency_check_ty (prog.get_ty_params ty_params);
           consistency_check_ty ty_im in

  let rec consistency_check_exp prev e =
    let node = prog.get_exp e in
    if prev <> node.prev
    then raise (ConsistencyError "Previous node pointer mismatch")
    else consistency_check_ty node.ty;
         match node.exp with
         | Hole -> ()
         | Var _ -> ()
         | StdLibRef _ -> ()

         | ValInt _ -> ()
         | ValBool _ -> ()

         | Empty -> ()
         | Cons (e1, e2) ->
           consistency_check_exp (Some e) e1;
           consistency_check_exp (Some e) e2
         | Match (e1, e2, (_, _, e3)) ->
           consistency_check_exp (Some e) e1;
           consistency_check_exp (Some e) e2;
           consistency_check_exp (Some e) e3

         | Let (_, rhs, body) ->
           consistency_check_exp (Some e) rhs;
           consistency_check_exp (Some e) body

         | Lambda (_, body) ->
           consistency_check_exp (Some e) body

         | Call (func, args) ->
           List.iter (consistency_check_exp (Some e)) args;
           consistency_check_exp (Some e) func

         | ExtLambda (params, body) ->
           let extvar = prog.params_extvar params in
           if not (List.mem params (prog.extvar_params extvar))
           then raise (ConsistencyError "params label not in extvar list")
           else consistency_check_exp (Some e) body

         | ExtCall (func, args) ->
           let extvar = prog.args_extvar args in
           if not (List.mem args (prog.extvar_args extvar))
           then raise (ConsistencyError "args label not in extvar list")
           else List.iter (consistency_check_exp (Some e)) (prog.get_args args);
                consistency_check_exp (Some e) func

         | If (pred, thn, els) ->
           consistency_check_exp (Some e) pred;
           consistency_check_exp (Some e) thn;
           consistency_check_exp (Some e) els

(*
         | Data {dcon=_; args=_} -> () (* todo *)
         | Match {arg=_; pats=_} -> () (* todo *)
*)
    in
  (* check that the argsvars points to params, ty_params, and args *)
  consistency_check_exp None prog.head

let rec string_of_ty prog ty =
  let string_of_ty_params ty_params =
    match ty_params with
    | [] -> ""
    | ty :: tys ->
      List.fold_left
        (fun acc ty -> string_of_ty prog ty ^ " " ^ acc)
        (string_of_ty prog ty)
        tys
  in
  match prog.get_ty ty with
  | TyNdBool -> "Bool"
  | TyNdInt -> "Int"
  | TyNdList ty' -> "(List " ^ string_of_ty prog ty' ^ ")"
  | TyNdArrow (params, ty_im) ->
    "(" ^ string_of_ty_params params ^ " -> " ^ string_of_ty prog ty_im ^ ")"
  | TyNdArrowExt (ty_params, ty_im) ->
    "(" ^ string_of_ty_params (prog.get_ty_params ty_params) ^ " -> " ^ string_of_ty prog ty_im ^ ")"


exception TypeCheckError of string

let rec is_same_ty prog tyl1 tyl2 =
  if tyl1 == tyl2
  then true
  else match (prog.get_ty tyl1, prog.get_ty tyl2) with
       | (TyNdBool, TyNdBool) -> true
       | (TyNdInt, TyNdInt) -> true
       | (TyNdArrowExt (params1, tyb1), TyNdArrowExt (params2, tyb2)) ->
         (prog.ty_params_extvar params1 == prog.ty_params_extvar params2)
         && List.for_all2 (is_same_ty prog) (prog.get_ty_params params1) (prog.get_ty_params params2)
         && is_same_ty prog tyb1 tyb2
       | (_, _) -> false

let is_func_producing prog tyl tylf =
  match prog.get_ty tylf with
  | TyNdArrow (_, tyb) -> is_same_ty prog tyl tyb
  | TyNdArrowExt (_, tyb) -> is_same_ty prog tyl tyb
  | _ -> false

let rec ty_compat_ty_label prog (ty : ty) (tyl : ty_label) acc =
  let check b = if b then Some acc else None in

  match ty, prog.get_ty tyl with
  | TyVar name, _ ->
    (match List.assoc_opt name acc with
     | None -> Some ((name, tyl) :: acc)
     | Some tyl' -> check (is_same_ty prog tyl tyl'))
  | TyInt, TyNdInt -> Some acc
  | TyBool, TyNdBool -> Some acc
  | TyList ty', TyNdList tyl' ->
    ty_compat_ty_label prog ty' tyl' acc
  | TyArrow (tys, ty'), TyNdArrow (tyls, tyl') ->
    if List.length tys == List.length tyls
    then List.fold_left2
           (fun acc ty tyl ->
              Option.bind acc (ty_compat_ty_label prog ty tyl))
           (ty_compat_ty_label prog ty' tyl' acc)
           (List.rev tys) tyls
    else None
  | _ -> None

(* type check *)
let type_check prog =
  (* TODO: better errors *)

  let ensure_same_extvar ex1 ex2 =
    if ex1 == ex2
    then ()
    else raise (TypeCheckError "extvar mismatch") in

  let ensure_same_ty tyl1 tyl2 =
    if is_same_ty prog tyl1 tyl2
    then ()
    else raise (TypeCheckError "Type mismatch") in

  let ensure_ty_compat ty tyl =
    match ty_compat_ty_label prog ty tyl [] with
    | None -> print_string (string_of_ty prog tyl); print_newline ();
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
       | Some (ty', _) -> ensure_ty_compat ty' node.ty; node.ty)

    | ValInt _ ->
      if (prog.get_ty node.ty) == TyNdInt
      then node.ty
      else raise (TypeCheckError "ValInt doesn't have type TyInt")

    | Empty ->
      (match (prog.get_ty node.ty) with
       | TyNdList _ -> node.ty
       | _ -> raise (TypeCheckError "Empty doesn't have list type"))

    | Cons (e1, e2) ->
      let ty1 = type_check_exp gamma e1 in
      let ty2 = type_check_exp gamma e2 in
      (match prog.get_ty ty2 with
       | TyNdList ty2' -> ensure_same_ty ty1 ty2'
       | _ -> raise (TypeCheckError "Cons doesn't have a list type"));
      node.ty

    | Match (e1, e2, (x, y, e3)) ->
      let ty1 = type_check_exp gamma e1 in
      let ty1' = (match prog.get_ty ty1 with
                  | TyNdList ty1' -> ty1'
                  | _ -> raise (TypeCheckError "Match scrutinee doesn't have list type")) in
      let ty2 = type_check_exp gamma e2 in
      let ty3 = type_check_exp ((x, ty1') :: (y, ty1) :: gamma) e3 in
      ensure_same_ty ty2 ty3;
      node.ty

    | ValBool _ ->
      if (prog.get_ty node.ty) == TyNdBool
      then node.ty
      else raise (TypeCheckError "ValBool doesn't have type TyBool")

    | Let (var, rhs, body) ->
      let rhs_ty = type_check_exp gamma rhs in
      let body_ty = type_check_exp ((var, rhs_ty) :: gamma) body in
      ensure_same_ty node.ty body_ty; node.ty

    | Lambda (vars, body) ->
      (match (prog.get_ty node.ty) with
       | TyNdArrow (tys, ty_im) ->
         let ty_body = type_check_exp ((List.combine vars tys) @ gamma) body in
         ensure_same_ty ty_body ty_im;
         node.ty
       | _ -> raise (TypeCheckError "lambda exp type not (closed) function type"))

    | Call (func, args) ->
      let func_ty = type_check_exp gamma func in
      (match (prog.get_ty func_ty) with
       | TyNdArrow (tys, ty_im) ->
         ensure_same_ty node.ty ty_im;
         type_check_args args tys;
         node.ty
       | _ -> raise (TypeCheckError "callee exp not (closed) function type"))

    (* todo: check and raise custom error when arg names and types
             have different lengths *)
    | ExtLambda (params, body) ->
      (match (prog.get_ty node.ty) with
       | TyNdArrowExt (ty_params, ty_im) ->
         ensure_same_extvar (prog.params_extvar params) (prog.ty_params_extvar ty_params);
         let vars = prog.get_params params in
         let tys = prog.get_ty_params ty_params in
         let ty_body = type_check_exp ((List.combine vars tys) @ gamma) body in
         ensure_same_ty ty_body ty_im;
         node.ty
       | _ -> raise (TypeCheckError "lambda exp type not (ext) function type"))

    | ExtCall (func, args) ->
      let func_ty = type_check_exp gamma func in
      (match (prog.get_ty func_ty) with
       | TyNdArrowExt (ty_params, ty_im) ->
         ensure_same_extvar (prog.args_extvar args) (prog.ty_params_extvar ty_params);
         ensure_same_ty node.ty ty_im;
         let exps = prog.get_args args in
         let tys = prog.get_ty_params ty_params in
         type_check_args exps tys;
         node.ty
       | _ -> raise (TypeCheckError "callee exp not (ext) function type"))

    | If (pred, thn, els) ->
      let typ = prog.get_ty (type_check_exp gamma pred) in
      if typ == TyNdBool
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


let rec string_of_exp prog e =
  let string_of_params params =
    match params with
    | [] -> ""
    | x :: xs ->
      List.fold_left
        (fun acc var -> Var.to_string var ^ ", " ^ acc)
        (Var.to_string x)
        xs
  in

  let string_of_args =
    List.fold_left
      (fun acc e -> " " ^ string_of_exp prog e ^ acc)
      ""
  in

  let node = prog.get_exp e in
  match node.exp with
  | Hole -> "[]"
  | StdLibRef str -> str
  | Var var -> Var.to_string var
  | Let (var, rhs, body) ->
    "(let " ^ Var.to_string var
    ^ " = " ^ string_of_exp prog rhs
    ^ " in " ^ string_of_exp prog body ^ ")"
  | Lambda (params, body) ->
    "(λ (" ^ string_of_params params ^ "). "
    ^ string_of_exp prog body ^ ")"
  | Call (func, args) ->
    "(" ^ string_of_exp prog func ^ string_of_args args ^ ")"
  | ExtLambda (params, body) ->
    "(λ (" ^ string_of_params (prog.get_params params)
    ^ " >" ^ ExtVar.to_string (prog.params_extvar params) ^ "). "
    ^ string_of_exp prog body ^ ")"
  | ExtCall (func, args) ->
    "(" ^ string_of_exp prog func ^ string_of_args (prog.get_args args)
    ^ " >" ^ ExtVar.to_string (prog.args_extvar args) ^ ")"
  | ValInt i -> Int.to_string i
  | ValBool b -> Bool.to_string b
  | Empty -> "[]"
  | Cons (e1, e2) -> "(" ^ string_of_exp prog e1 ^ " :: " ^ string_of_exp prog e2 ^ ")"
  | Match (e1, e2, (x, y, e3)) ->
    "(match " ^ string_of_exp prog e1 ^ " with"
    ^ " | [] -> " ^ string_of_exp prog e2
    ^ " | " ^ Var.to_string x ^ " :: " ^ Var.to_string y
    ^ " -> " ^ string_of_exp prog e3 ^ ")"
  | If (pred, thn, els) ->
    "(if " ^ string_of_exp prog pred
    ^ " then " ^ string_of_exp prog thn
    ^ " else " ^ string_of_exp prog els ^ ")"
(*
type exp =
  | Lambda of {
      params : params_label;
      body : exp_label;
    }
  | Call of {
      func : exp_label;
      args : args_label;
      }
 *)

let string_of_prog prog = string_of_exp prog prog.head
