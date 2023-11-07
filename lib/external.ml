(* file for datatypes used outside generator internals *)

open Util

(* external types datatype *)
type ty =
  | TyCons of string * ty list
  | TyFun of ty list * ty
  | TyVar of string

let rec ty_vars ty =
  match ty with
  | TyVar a -> SS.singleton a
  | TyCons (_, ty_args) ->
     SS.union_seq (Seq.map ty_vars (List.to_seq ty_args))
  | TyFun (arg_tys, ty_body) ->
     SS.union (SS.union_seq (Seq.map ty_vars (List.to_seq arg_tys)))
              (ty_vars ty_body)

type exp =
  | Ref of string * ty
  | Call of exp * exp list
  | Lambda of (string * ty) list * exp
  | Let of (string * ty) * exp * exp
