
(*
   Types
 *)

(* type variables for polymorphism *)
module TyVar = Key.Make (struct let x="a" end)
type ty_var = TyVar.t

(* type labels *)
module TypeLabel = Key.Make (struct let x="ty" end)
type ty_label = TypeLabel.t

(* extension variables *)
module ExtVar = Key.Make (struct let x="ext" end)
type extvar = ExtVar.t

(* types for data pointers *)
module DataTy = Key.Make (struct let x="d" end)

(* type parameter variables for extensible arrow types *)
module TyParamsLabel = Key.Make (struct let x="p" end)
type ty_params_label = TyParamsLabel.t

(* type datatype *)
type ty = (* TyArrow of ty_label list * ty_label *)
  | TyInt
  | TyBool
  | TyList of ty_label
  | TyArrow of (ty_label list) * ty_label
  | TyArrowExt of ty_params_label * ty_label
  | TyVar of ty_var
(*type ty_node = {ty : ty}*)

(* type tree datatype *)
type flat_ty =
  | FlatTyInt
  | FlatTyBool
  | FlatTyList of flat_ty
  | FlatTyArrow of (flat_ty list) * flat_ty
  | FlatTyVar of string

let rec flat_ty_vars (t : flat_ty) =
  match t with
  | FlatTyVar x -> Util.SS.singleton x
  | FlatTyBool | FlatTyInt -> Util.SS.empty
  | FlatTyList t' -> flat_ty_vars t'
  | FlatTyArrow (ts, t') -> List.fold_left Util.SS.union (flat_ty_vars t') (List.map flat_ty_vars ts)


type registry = {
    (*
    mutable extvars : list extvar;
    mutable ty_params : list ty_param;
     *)

    (* type operations *)
    new_ty : ty -> ty_label;
    get_ty : ty_label -> ty;

    (* unresolved polymorphic variable operations *)
    new_ty_var : unit -> ty_var;
    get_ty_var : ty_var -> ty_label list;
    set_ty_var : ty_var -> ty -> unit;

    (* extension variable operations *)
    new_extvar : unit -> extvar;

    (* type parameter operations *)
    new_ty_params : extvar -> ty_params_label;
    get_ty_params : ty_params_label -> ty_label list;
    add_ty_param : ty_params_label -> ty_label -> unit;

    (* all params labels that are associated with the given extvar *)
    extvar_ty_params : extvar -> ty_params_label list;
    ty_params_extvar : ty_params_label -> extvar;

    flat_ty_to_ty : flat_ty -> ty_label;
  }

let consistency_check ty_registry ty0 = 
  let rec consistency_check_ty ty =
    match ty_registry.get_ty ty with
    | TyBool -> ()
    | TyInt -> ()
    | TyList ty' -> consistency_check_ty ty'
    | TyArrow (params, ty_im) ->
      List.iter consistency_check_ty params;
      consistency_check_ty ty_im
    | TyArrowExt (ty_params, ty_im) ->
      let extvar = ty_registry.ty_params_extvar ty_params in
      if not (List.mem ty_params (ty_registry.extvar_ty_params extvar))
      then raise (Util.ConsistencyError "ty_params label not in extvar list")
      else List.iter consistency_check_ty (ty_registry.get_ty_params ty_params);
           consistency_check_ty ty_im
    | TyVar a ->
      if not (List.mem ty (ty_registry.get_ty_var a))
      then raise (Util.ConsistencyError "ty_var label not in ty_var list")
      else () in
  consistency_check_ty ty0


let make () (*?(std_lib = [])*) =
  let ty_tbl : ty TypeLabel.Tbl.t = TypeLabel.Tbl.create 100 in
  let ty_var_tbl : (ty_label list) TyVar.Tbl.t = TyVar.Tbl.create 100 in
  let ty_params_tbl : (ty_label list) TyParamsLabel.Tbl.t = TyParamsLabel.Tbl.create 100 in
  let extvar_ty_params_tbl : (ty_params_label list) ExtVar.Tbl.t = ExtVar.Tbl.create 100 in
  let ty_params_extvar_tbl : extvar TyParamsLabel.Tbl.t = TyParamsLabel.Tbl.create 100 in

  let new_extvar () =
    let extvar = ExtVar.make () in
    ExtVar.Tbl.add extvar_ty_params_tbl extvar [];
    extvar in

  let new_ty_var () =
    let tyvar = TyVar.make () in
    TyVar.Tbl.add ty_var_tbl tyvar [];
    tyvar in

  let get_ty_var a = TyVar.Tbl.find ty_var_tbl a in
  let add_ty_var_ref a lbl = TyVar.Tbl.replace ty_var_tbl a (lbl :: get_ty_var a) in

  let set_ty_var a ty =
    List.iter (fun tyl ->
                 TypeLabel.Tbl.replace ty_tbl tyl ty;
                 match ty with
                 | TyVar b -> add_ty_var_ref b tyl
                 | _ -> ())
              (TyVar.Tbl.find ty_var_tbl a);
    (* type variables can only be set once *)
    TyVar.Tbl.remove ty_var_tbl a in

  let new_ty =
    let bool_lab = TypeLabel.make () in
    TypeLabel.Tbl.add ty_tbl bool_lab TyBool;
    let int_lab = TypeLabel.make () in
    TypeLabel.Tbl.add ty_tbl int_lab TyInt;
    fun ty' ->
      match ty' with
      | TyBool -> bool_lab
      | TyInt -> int_lab
      | _ ->
        let lab = TypeLabel.make () in
        (match ty' with
         | TyVar a -> add_ty_var_ref a lab
         | _ -> ());
        TypeLabel.Tbl.add ty_tbl lab ty';
        lab in
  let get_ty lab = TypeLabel.Tbl.find ty_tbl lab in

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

  let flat_ty_to_ty ty =
    let vars = Util.SM.of_seq (Seq.map (fun a -> (a, new_ty_var ())) (Util.SS.to_seq (flat_ty_vars ty))) in
    let rec lp ty =
      let ty' = match ty with
        | FlatTyVar a -> TyVar (Util.SM.find a vars)
        | FlatTyInt -> TyInt
        | FlatTyBool -> TyBool
        | FlatTyList ty'' -> TyList (lp ty'')
        | FlatTyArrow (params, res) -> TyArrow (List.rev_map lp params, lp res) in
      new_ty ty'
    in lp ty in

  {
    new_extvar = new_extvar;
    new_ty = new_ty;
    get_ty = get_ty;

    new_ty_var = new_ty_var;
    get_ty_var = get_ty_var;
    set_ty_var = set_ty_var;

    new_ty_params = new_ty_params;
    get_ty_params = get_ty_params;
    add_ty_param = add_ty_param;

    extvar_ty_params = extvar_ty_params;
    ty_params_extvar = ty_params_extvar;

    flat_ty_to_ty = flat_ty_to_ty;
  }


let rec contains_ty_var ty_registry a tyl =
  match ty_registry.get_ty tyl with
  | TyVar b -> TyVar.equal a b
  | TyBool | TyInt -> false
  | TyList tyl' -> contains_ty_var ty_registry a tyl'
  | TyArrow (tys, tyb) ->
    contains_ty_var ty_registry a tyb || List.exists (contains_ty_var ty_registry a) tys
  | TyArrowExt (params, tyb) ->
    contains_ty_var ty_registry a tyb ||
    List.exists (contains_ty_var ty_registry a) (ty_registry.get_ty_params params)

(* TODO: same ty modulo type variable resolution *)
let rec is_same_ty ty_registry tyl1 tyl2 =
  if TypeLabel.equal tyl1 tyl2
  then true
  else match (ty_registry.get_ty tyl1, ty_registry.get_ty tyl2) with
       | (TyBool, TyBool) -> true
       | (TyInt, TyInt) -> true
       | (TyList tyl1', TyList tyl2') -> is_same_ty ty_registry tyl1' tyl2'
       | (TyArrowExt (params1, tyb1), TyArrowExt (params2, tyb2)) ->
         (ty_registry.ty_params_extvar params1 == ty_registry.ty_params_extvar params2)
         && List.for_all2 (is_same_ty ty_registry) (ty_registry.get_ty_params params1) (ty_registry.get_ty_params params2)
         && is_same_ty ty_registry tyb1 tyb2
       | (TyArrow (tyls1, tyb1), TyArrow (tyls2, tyb2)) ->
         List.length tyls1 = List.length tyls2
         && List.for_all2 (is_same_ty ty_registry) tyls1 tyls2
         && is_same_ty ty_registry tyb1 tyb2
       | (TyVar a, TyVar b) -> TyVar.equal a b
       | (_, _) -> false

let is_func_producing ty_registry tyl tylf =
  match ty_registry.get_ty tylf with
  | TyArrow (_, tyb) -> is_same_ty ty_registry tyl tyb
  | TyArrowExt (_, tyb) -> is_same_ty ty_registry tyl tyb
  | _ -> false

(* FIXME: why does this use an assoc list?? *)
let ty_compat_ty_label (ty_registry : registry) =
  let rec compat_lp acc1 acc2 (ty : flat_ty) (tyl : ty_label) =
    let check b = if b then Some (acc1, acc2) else None in

    match ty, ty_registry.get_ty tyl with
    | FlatTyVar name, _ ->
      (match List.assoc_opt name acc1 with
       | None -> Some ((name, tyl) :: acc1, acc2)
       | Some tyl' -> check (is_same_ty ty_registry tyl tyl'))
    | _, TyVar a ->
      (* TODO: deal with this massive headache of a problem of full type variable resolution *)
      if Util.SS.is_empty (flat_ty_vars ty)
      then match List.assoc_opt a acc2 with
           | None -> Some (acc1, (a, ty) :: acc2)
           | Some ty' -> check (ty = ty')
      else None
    | FlatTyInt, TyInt -> Some (acc1, acc2)
    | FlatTyBool, TyBool -> Some (acc1, acc2)
    | FlatTyList ty', TyList tyl' ->
      compat_lp acc1 acc2 ty' tyl'
    | FlatTyArrow (tys, ty'), TyArrow (tyls, tyl') ->
      if List.length tys == List.length tyls
      then List.fold_left2
             (fun acc ty tyl ->
                Option.bind acc (fun acc -> compat_lp (fst acc) (snd acc) ty tyl))
             (compat_lp acc1 acc2 ty' tyl')
             (List.rev tys) tyls
      else None
    | _ -> None in
  compat_lp [] []


let rec string_of ty_registry ty =
  let string_of_params ty_params =
    match ty_params with
    | [] -> ""
    | ty :: tys ->
      List.fold_left
        (fun acc ty -> string_of ty_registry ty ^ " " ^ acc)
        (string_of ty_registry ty)
        tys
  in
  match ty_registry.get_ty ty with
  | TyBool -> "Bool"
  | TyInt -> "Int"
  | TyList ty' -> "(List " ^ string_of ty_registry ty' ^ ")"
  | TyArrow (params, ty_im) ->
    "(" ^ string_of_params params ^ " -> " ^ string_of ty_registry ty_im ^ ")"
  | TyArrowExt (ty_params, ty_im) ->
    "(" ^ string_of_params (ty_registry.get_ty_params ty_params) ^ " -> " ^ string_of ty_registry ty_im ^ ")"
  | TyVar a -> TyVar.to_string a
