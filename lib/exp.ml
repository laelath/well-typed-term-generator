
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
  | TyArrowExt of {
      ty_params : ty_params_label;
      ty_im : ty_label;
    }
  | TyData of {
      dcon_ty : DataTy.t;
      arg_tys : ty_label list;
    }
     (* | TyVar of ty_var *)
type ty_node = TyNode of {ty : ty}

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
  | Var of {
      var : var;
    }
  | Let of {
      var : var; 
      rhs : exp_label; 
      body : exp_label;
    }
  (* perhaps we want to separate extensible lambdas and calls 
     from non-extensible ones *)
  | Lambda of {
      params : params_label;
      body : exp_label;
    }
  | Call of {
      func : exp_label; 
      args : args_label;
    }
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
(* | Prim of prim * label list *)

(* expression nodes *)
type exp_node = ExpNode of {
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

  let new_ty node =
    let lab = TypeLabel.make() in
    let () = TypeLabel.Tbl.add ty_tbl lab node in
    lab in
  let get_ty lab = TypeLabel.Tbl.find ty_tbl lab in

  let new_exp node =
    let lab = ExpLabel.make() in
    let () = ExpLabel.Tbl.add exp_tbl lab node in
    lab in
  let get_exp lab = ExpLabel.Tbl.find exp_tbl lab in
  let set_exp lab node = ExpLabel.Tbl.replace exp_tbl lab node in

  let new_ty_params extvar =
    let lab = TyParamsLabel.make() in
    let () = TyParamsLabel.Tbl.add ty_params_tbl lab [] in
    let () = ExtVar.Tbl.replace extvar_ty_params_tbl extvar
                                (lab :: (ExtVar.Tbl.find extvar_ty_params_tbl extvar)) in
    let () = TyParamsLabel.Tbl.add ty_params_extvar_tbl lab extvar in
    lab in
  let get_ty_params lab = TyParamsLabel.Tbl.find ty_params_tbl lab in
  let add_ty_param lab ty = 
    let () = TyParamsLabel.Tbl.replace ty_params_tbl lab
                                       (ty :: (TyParamsLabel.Tbl.find ty_params_tbl lab)) in
    () in
  let extvar_ty_params extvar = ExtVar.Tbl.find extvar_ty_params_tbl extvar in
  let ty_params_extvar lab = TyParamsLabel.Tbl.find ty_params_extvar_tbl lab in

  let new_params extvar =
    let lab = ParamsLabel.make() in
    let () = ParamsLabel.Tbl.add params_tbl lab [] in
    let () = ExtVar.Tbl.replace extvar_params_tbl extvar
                                (lab :: (ExtVar.Tbl.find extvar_params_tbl extvar)) in
    let () = ParamsLabel.Tbl.add params_extvar_tbl lab extvar in
    lab in
  let get_params lab = ParamsLabel.Tbl.find params_tbl lab in
  let add_param lab var = 
    let () = ParamsLabel.Tbl.replace params_tbl lab
                                       (var :: (ParamsLabel.Tbl.find params_tbl lab)) in
    () in
  let extvar_params extvar = ExtVar.Tbl.find extvar_params_tbl extvar in
  let params_extvar lab = ParamsLabel.Tbl.find params_extvar_tbl lab in
  

  let new_args extvar parent =
    let lab = ArgsLabel.make() in
    let () = ArgsLabel.Tbl.add args_tbl lab [] in
    let () = ExtVar.Tbl.replace extvar_args_tbl extvar
                                (lab :: (ExtVar.Tbl.find extvar_args_tbl extvar)) in
    let () = ArgsLabel.Tbl.add args_extvar_tbl lab extvar in
    let () = ArgsLabel.Tbl.add args_parent_tbl lab parent in
    lab in
  let get_args lab = ArgsLabel.Tbl.find args_tbl lab in
  let add_arg lab node = 
    let () = ArgsLabel.Tbl.replace args_tbl lab
                                       (node :: (ArgsLabel.Tbl.find args_tbl lab)) in
    () in
  let extvar_args extvar = ExtVar.Tbl.find extvar_args_tbl extvar in
  let args_extvar lab = ArgsLabel.Tbl.find args_extvar_tbl lab in
  let args_parent lab = ArgsLabel.Tbl.find args_parent_tbl lab in
  
  let head = new_exp (ExpNode {exp=Hole; ty=new_ty (TyNode {ty=ty}); prev=None}) in

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


(* check that the prev pointers are correct, and that each node points to itself *)
let consistencyCheck _ = ()
(* type check *)
let typeCheck _ = ()
(* perform the checks *)
let check prog = (
    consistencyCheck prog;
    typeCheck prog;
    ()
  )

