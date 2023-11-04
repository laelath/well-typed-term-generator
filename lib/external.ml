(* external types datatype *)
type ty =
  | TyCons of string * ty list
  | TyFun of ty list * ty
  | TyVar of string

let rec ty_vars ty =
  match ty with
  | TyCons (_, ty_args) ->
    Util.union_map ty_vars ty_args
  | TyFun (arg_tys, ty_body) ->
    Util.SS.union (Util.union_map ty_vars arg_tys) (ty_vars ty_body)
  | TyVar a ->
    Util.SS.singleton a
