
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
        | TyArrowExt of ty_params_label * ty_label
        | TyData of DataTy.t * (ty_label list)
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
    get_args : args_label -> var list;
    new_args : extvar -> args_label;
    add_arg : args_label -> exp_label -> unit;
    (* the node that contains this args label *)
    args_prev : args_label -> exp_label;
    (* all args labels that are associated with the given extvar *)
    extvar_args : extvar -> args_label list;
    args_extvar : args_label -> extvar;

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

