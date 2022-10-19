
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
type ty = (* TyArrow of ty_label list * ty_label *)
  | TyInt
  | TyBool
  | TyArrowExt of ty_params_label * ty_label
  (* | TyVar of ty_var *)
type ty_node = {ty : ty}

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
  | Let of (var * exp_label * exp_label)
  (* perhaps we want to separate extensible lambdas and calls
     from non-extensible ones *)
  | Lambda of (params_label * exp_label)
  | Call of (exp_label * args_label)
  | ValInt of int
  | ValBool of bool
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
    head : exp_label;

    (* variable operations *)
    new_var : unit -> var;
    (* extension variable operations *)
    new_extvar : unit -> extvar;

    (* type operations *)
    new_ty : ty -> ty_label;
    get_ty : ty_label -> ty;

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

  }

let make_program ty =
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
  let new_extvar () = ExtVar.make () in

  (* TODO: actually use the int and bool labels *)
  let new_ty =
    let bool_lab = TypeLabel.make () in
    TypeLabel.Tbl.add ty_tbl bool_lab {ty=TyBool};
    let int_lab = TypeLabel.make () in
    TypeLabel.Tbl.add ty_tbl int_lab {ty=TyInt};
    fun ty' ->
      match ty' with
      | TyBool -> bool_lab
      | TyInt -> int_lab
      | _ ->
        let lab = TypeLabel.make () in
        TypeLabel.Tbl.add ty_tbl lab {ty=ty'};
        lab in
  let get_ty lab = (TypeLabel.Tbl.find ty_tbl lab).ty in

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

  let head = new_exp {exp=Hole; ty=new_ty ty; prev=None} in

  {
    head = head;

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

  }

let rec lookup gamma x =
  match gamma with
  | [] -> None
  | (y, ty) :: gamma' ->
    if x == y
    then Some ty
    else lookup gamma' x

exception ConsistencyError of string

(* check that the prev pointers are correct,
   and that each node points to itself *)
let consistencyCheck prog =

  let rec consistencyCheckTy ty =
    match prog.get_ty ty with
    | TyBool -> ()
    | TyInt -> ()
    | TyArrowExt (ty_params, ty_im) ->
      let extvar = prog.ty_params_extvar ty_params in
      if not (List.mem ty_params (prog.extvar_ty_params extvar))
      then raise (ConsistencyError "ty_params label not in extvar list")
      else List.iter consistencyCheckTy (prog.get_ty_params ty_params);
           consistencyCheckTy ty_im in

  let rec consistencyCheckExp prev e =
    let node = prog.get_exp e in
    if prev != node.prev
    then raise (ConsistencyError "Previous node pointer mismatch")
    else consistencyCheckTy node.ty;
         match node.exp with
         | Hole -> ()
         | Var _ -> ()

         | ValInt _ -> ()
         | ValBool _ -> ()

         | Let (_, rhs, body) ->
           consistencyCheckExp (Some e) rhs;
           consistencyCheckExp (Some e) body

         | Lambda (params, body) ->
           let extvar = prog.params_extvar params in
           if not (List.mem params (prog.extvar_params extvar))
           then raise (ConsistencyError "params label not in extvar list")
           else consistencyCheckExp (Some e) body

         | Call (func, args) ->
           let extvar = prog.args_extvar args in
           if not (List.mem args (prog.extvar_args extvar))
           then raise (ConsistencyError "args label not in extvar list")
           else List.iter (consistencyCheckExp (Some e)) (prog.get_args args);
                consistencyCheckExp (Some e) func

         | If (pred, thn, els) ->
           consistencyCheckExp (Some e) pred;
           consistencyCheckExp (Some e) thn;
           consistencyCheckExp (Some e) els

(*
         | Data {dcon=_; args=_} -> () (* todo *)
         | Match {arg=_; pats=_} -> () (* todo *)
*)
    in
  (* check that the argsvars points to params, ty_params, and args *)
  consistencyCheckExp None prog.head

exception TypeCheckError of string

(* type check *)
let typeCheck prog =
  (* TODO: better errors *)

  let ensureSameExtvar ex1 ex2 =
    if ex1 == ex2
    then ()
    else raise (TypeCheckError "extvar mismatch") in

  let rec ensureSameTy tyl1 tyl2 =
    if tyl1 == tyl2
    then ()
    else let ty1 = prog.get_ty tyl1 in
         let ty2 = prog.get_ty tyl2 in
         match (ty1, ty2) with
         | (TyBool, TyBool) -> ()
         | (TyInt, TyInt) -> ()
         | (TyArrowExt (params1, tyb1), TyArrowExt (params2, tyb2)) ->
           ensureSameExtvar (prog.ty_params_extvar params1) (prog.ty_params_extvar params2);
           List.iter2 ensureSameTy (prog.get_ty_params params1) (prog.get_ty_params params2);
           ensureSameTy tyb1 tyb2
         | (_, _) -> raise (TypeCheckError "Type mismatch") in

  let rec typeCheckExp gamma e =
    let node = prog.get_exp e in
    match node.exp with
    | Hole -> node.ty
    | Var var ->
      (match lookup gamma var with
       | None -> raise (TypeCheckError "Variable not in scope")
       | Some ty' -> ensureSameTy node.ty ty'; node.ty)

    | ValInt _ ->
      if (prog.get_ty node.ty) == TyInt
      then node.ty
      else raise (TypeCheckError "ValInt doesn't have type TyInt")

    | ValBool _ ->
      if (prog.get_ty node.ty) == TyBool
      then node.ty
      else raise (TypeCheckError "ValBool doesn't have type TyBool")

    | Let (var, rhs, body) ->
      let rhs_ty = typeCheckExp gamma rhs in
      let body_ty = typeCheckExp ((var, rhs_ty) :: gamma) body in
      ensureSameTy node.ty body_ty; node.ty

    (* todo: check and raise custom error when arg names and types
             have different lengths *)
    | Lambda (params, body) ->
      (match (prog.get_ty node.ty) with
       | TyArrowExt (ty_params, ty_im) ->
         ensureSameExtvar (prog.params_extvar params) (prog.ty_params_extvar ty_params);
         let vars = prog.get_params params in
         let tys = prog.get_ty_params ty_params in
         let ty_body = typeCheckExp ((List.combine vars tys) @ gamma) body in
         ensureSameTy ty_body ty_im; node.ty
       | _ -> raise (TypeCheckError "lambda exp type not function type"))

    | Call (func, args) ->
      let rec typeCheckArgs exps tys =
        (match (exps, tys) with
         | ([], []) -> ()
         | (exp :: exps', ty :: tys') ->
           let ty' = typeCheckExp gamma exp in
           ensureSameTy ty ty';
           typeCheckArgs exps' tys'
         | _ -> raise (TypeCheckError "number of function call args differs from type")) in
      let func_ty = typeCheckExp gamma func in
      (match (prog.get_ty func_ty) with
       | TyArrowExt (ty_params, ty_im) ->
         ensureSameExtvar (prog.args_extvar args) (prog.ty_params_extvar ty_params);
         ensureSameTy node.ty ty_im;
         let exps = prog.get_args args in
         let tys = prog.get_ty_params ty_params in
         typeCheckArgs exps tys;
         node.ty
       | _ -> raise (TypeCheckError "callee exp not function type"))

    | If (pred, thn, els) ->
      let typ = prog.get_ty (typeCheckExp gamma pred) in
      if typ == TyBool
      then (ensureSameTy node.ty (typeCheckExp gamma thn);
            ensureSameTy node.ty (typeCheckExp gamma els);
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
  let _ = typeCheckExp [] prog.head in
  ()

(* perform the checks *)
let check prog = (
    consistencyCheck prog;
    typeCheck prog;
    ()
  )


let rec string_of_ty prog ty =
  let string_of_ty_params ty_params =
    match prog.get_ty_params ty_params with
    | [] -> ""
    | ty :: tys ->
      List.fold_left
        (fun acc ty -> string_of_ty prog ty ^ " " ^ acc)
        (string_of_ty prog ty)
        tys
  in
  match prog.get_ty ty with
  | TyBool -> "Bool"
  | TyInt -> "Int"
  | TyArrowExt (ty_params, ty_im) ->
    string_of_ty_params ty_params ^ " -> " ^ string_of_ty prog ty_im


let rec string_of_exp prog e =
  let string_of_params params =
    match prog.get_params params with
    | [] -> ""
    | x :: xs ->
      List.fold_left
        (fun acc var -> Var.to_string var ^ ", " ^ acc)
        (Var.to_string x)
        xs
  in

  let string_of_args args =
    List.fold_left
      (fun acc e -> " (" ^ string_of_exp prog e ^ ")" ^ acc)
      ""
      (prog.get_args args)
  in

  let node = prog.get_exp e in
  match node.exp with
  | Hole -> "[]"
  | Var var -> Var.to_string var
  | Let (var, rhs, body) ->
    "let " ^ Var.to_string var
    ^ " = " ^ string_of_exp prog rhs
    ^ " in " ^ string_of_exp prog body
  | Lambda (params, body) ->
    "λ (" ^ string_of_params params
    ^ " >" ^ ExtVar.to_string (prog.params_extvar params) ^ "). "
    ^ string_of_exp prog body
  | Call (func, args) ->
    "(" ^ string_of_exp prog func ^ string_of_args args
    ^ " >" ^ ExtVar.to_string (prog.args_extvar args) ^ ")"
  | ValInt i -> Int.to_string i
  | ValBool b -> Bool.to_string b
  | If (pred, thn, els) ->
    "if " ^ string_of_exp prog pred
    ^ " then " ^ string_of_exp prog thn
    ^ " else " ^ string_of_exp prog els
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
