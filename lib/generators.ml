
(* TODO:
   - remove from Urn
   - on Urn insert check if weight is 0
   - factor out constructor steps (can we avoid duplicating of type check?)
   -
 *)

(*
  UTIL
 *)

type hole_info = Rules.hole_info

(* finds all the variables in scope of a hole *)
let find_vars (prog : Exp.program) (e : Exp.exp_label) =
  let rec find_binds (e : Exp.exp_label) =
    match (prog.get_exp e).prev with
    | None -> []
    | Some ep ->
      let node = prog.get_exp ep in
      let exp_binds =
        match node.exp with
         | Let (x, rhs, body) ->
           if (e == body)
           then [(x, (prog.get_exp rhs).ty)]
           else []
         | Match (scr, _, (fst, rst, body)) ->
           if (e == body)
           then let lst_ty = (prog.get_exp scr).ty in
                match prog.ty.get_ty lst_ty with
                | TyList ty' -> [(fst, ty'); (rst, lst_ty)]
                | _ -> raise (Util.Impossible "match scrutinee does not have list type")
           else []
         | Lambda (params, _) ->
           (match prog.ty.get_ty node.ty with
            | TyArrow (ty_params, _) -> List.combine params ty_params
            | _ -> raise (Util.Impossible "lambda does not have arrow type"))
         | ExtLambda (params, _) ->
           (match prog.ty.get_ty node.ty with
            | TyArrowExt (ty_params, _) -> List.combine (prog.get_params params) (prog.ty.get_ty_params ty_params)
            | _ -> raise (Util.Impossible "lambda does not have arrow type"))
         | _ -> [] in
      exp_binds @ find_binds ep
  in
  find_binds e

(* takes E[e] and finds all lambdas i such that E_1[lambda_i xs . E_2[e]] *)
let find_enclosing_lambdas (prog : Exp.program) (e : Exp.exp_label) : (Exp.params_label list) =
  let rec find_ext_vars ty =
    match prog.ty.get_ty ty with
    | TyBool | TyInt | TyVar _ -> Type.ExtVar.Set.empty
    | TyList ty' -> find_ext_vars ty'
    | TyArrow (params, ty') ->
      List.fold_left
        (fun acc ty' -> Type.ExtVar.Set.union acc (find_ext_vars ty'))
        (find_ext_vars ty') params
    | TyArrowExt (params, ty') ->
      Type.ExtVar.Set.add
        (prog.ty.ty_params_extvar params)
        (List.fold_left
          (fun acc ty' -> Type.ExtVar.Set.union acc (find_ext_vars ty'))
          (find_ext_vars ty')
          (prog.ty.get_ty_params params))
  in

  let node = prog.get_exp e in
  let extvars = find_ext_vars node.ty in

  let rec find_enc ep acc =
    match ep with
    | None -> acc
    | Some e ->
      let node' = prog.get_exp e in
      match node'.exp with
      | ExtLambda (params, _) ->
        if not (Type.ExtVar.Set.mem (prog.params_extvar params) extvars)
           && (Random.int (List.length (prog.get_params params) + 1) == 0)
        then find_enc node'.prev (params :: acc)
        else find_enc node'.prev acc
      | _ -> find_enc node'.prev acc
  in
  find_enc node.prev []

let exp_depth (prog : Exp.program) (e : Exp.exp_label) =
  let rec exp_depth' e acc =
    let node = prog.get_exp e in
    match node.prev with
    | None -> acc
    | Some e' -> exp_depth' e' (acc + 1) in
  exp_depth' e 0

let is_list_ty (prog : Exp.program) ty =
  match prog.ty.get_ty ty with
  | Type.TyList _ -> true
  | _ -> false

let find_std_lib_refs (prog : Exp.program) tyl filter =
  List.filter_map
    (fun (x, ty) ->
       if filter (x, ty)
       then Option.map (fun (_, mp) -> (x, mp)) (Type.ty_compat_ty_label prog.ty ty tyl)
       else None)
    prog.std_lib

(* finds all functions in the standard library that can produce tyl *)
let find_std_lib_funcs (prog : Exp.program) tyl filter =
  List.filter_map
    (fun (x, ty) ->
       if filter (x, ty)
       then match ty with
            | Type.FlatTyArrow (tys, ty') ->
              (match Type.ty_compat_ty_label prog.ty ty' tyl with
               | None -> None
               | Some mp -> Some (x, ty, tys, mp))
            | _ -> None
       else None)
    prog.std_lib



(*
  TRANSITIONS
 *)

type rule_urn = (unit -> Exp.exp_label list) Urn.t

let steps_generator (prog : Exp.program) (hole : hole_info) (acc : rule_urn)
                    (rule : Exp.program -> hole_info -> 'a -> unit -> Exp.exp_label list)
                    (weight : hole_info -> 'a -> float)
                    (collection : 'a list) =
  List.fold_left (fun acc a ->
                  Urn.insert acc (weight hole a) (Urn.Value (rule prog hole a)))
             acc collection

let bucket (bucket_weight : Exp.program -> hole_info -> float) steps (weight : Exp.program -> hole_info -> int) (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let nested = fun () -> steps weight prog hole acc in
  Urn.insert acc (bucket_weight prog hole) (Urn.Nested nested)

let singleton_generator weight f prog hole acc =
  Urn.insert acc (weight hole ()) (Urn.Value (f prog hole))



let not_useless_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let params = find_enclosing_lambdas prog hole.label in
  steps_generator prog hole acc
                  Rules.not_useless_step weight params

let palka_rule_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let funcs = List.filter (fun b -> Type.is_func_producing prog.ty hole.ty_label (snd b)) hole.vars in
  steps_generator prog hole acc
                  Rules.palka_rule_step weight funcs

let let_insertion_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  steps_generator prog hole acc
                  Rules.let_insertion_step weight (List.init (hole.depth + 1) (fun x -> x))

let match_insertion_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let all_depths = List.init (hole.depth + 1) (fun x -> x) in
  let acc = steps_generator prog hole acc
                            Rules.match_insertion_step weight all_depths in
  match prog.ty.get_ty hole.ty_label with
  | TyList _ ->
     steps_generator prog hole acc
                     Rules.match_insertion_list_step weight all_depths
  | _ -> acc




let create_match_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let lists = List.filter (fun b -> is_list_ty prog (snd b)) hole.vars in
  steps_generator prog hole acc
                  Rules.create_match_step weight lists

let var_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let ref_vars = List.filter (fun b -> Type.is_same_ty prog.ty (snd b) hole.ty_label) hole.vars in
  steps_generator prog hole acc
                  Rules.var_step weight ref_vars

let resolve_ty_var_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let var_vars = List.filter_map
                   (fun b -> match prog.ty.get_ty (snd b) with
                             | Type.TyVar a when not (Type.contains_ty_var prog.ty a hole.ty_label) -> Some (fst b, a)
                             | _ -> None) hole.vars in
  steps_generator prog hole acc
                  Rules.resolve_ty_var_step weight var_vars


let std_lib_steps multiplier weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let valid_refs = find_std_lib_refs prog hole.ty_label (fun _ -> true) in
  (* TODO: FIXME: GROSS: HACK: *)
  (* BEN: Less gross? do we want to handle the std lib palka this rule symmetrically? *)
  let weight' hi (x, _) = (weight hi x) *. (multiplier x) in
  steps_generator prog hole acc
                  Rules.std_lib_step weight' valid_refs


let std_lib_palka_rule_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let valid_refs = find_std_lib_funcs prog hole.ty_label (fun _ -> true) in

  steps_generator prog hole acc
                  Rules.std_lib_palka_rule_step weight valid_refs


let base_constructor_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  (* TODO: sample base type (in this case, just Int) *)
  match prog.ty.get_ty hole.ty_label with
  | TyInt ->
     let vals = [Exp.ValInt 0; Exp.ValInt 1; Exp.ValInt 2; Exp.ValInt (-1); Exp.ValInt 42] in
     steps_generator prog hole acc
                     Rules.base_constructor_step weight vals
  | _ -> acc

let data_constructor_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  (* FUTURE: loop over data constructors for type each gets a rule *)
  (* FUTURE: disincentivize nested data constructors. Maybe these rules all get weight 1, and there's a seperate rule for data cons that add holes that gets a higher weight when not nested. *)
  let vals = match prog.ty.get_ty hole.ty_label with
    | TyBool -> ["true"; "false"]
    | TyList _ -> ["nil"; "cons"]
    | _ -> [] in
  steps_generator prog hole acc
                  Rules.data_constructor_step weight vals

let func_constructor_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  match prog.ty.get_ty hole.ty_label with
  | TyArrow _ | TyArrowExt _ ->
     singleton_generator weight Rules.func_constructor_step prog hole acc
  | _ -> acc


let lambda_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  match prog.ty.get_ty hole.ty_label with
  | TyArrow _ ->
    singleton_generator weight Rules.func_constructor_step prog hole acc
  | _ -> acc

let ext_lambda_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  match prog.ty.get_ty hole.ty_label with
  | TyArrowExt _ ->
    singleton_generator weight Rules.func_constructor_step prog hole acc
  | _ -> acc

(* fills the hole with a seq where the lhs is a variable *)
let palka_seq_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  (* technically palka can put std lib functions in the seq position... *)
  (* ... but we'll just ignore that *)
  steps_generator prog hole acc
                  Rules.seq_step weight hole.vars


type t = ((Exp.program -> hole_info -> rule_urn -> rule_urn) list)

let c (w : float) (_ : hole_info) _ = w
let w_const n = c n
let w_fuel_base n m (hole : hole_info) _ = Int.to_float hole.fuel *. n +. m
let w_fuel_depth n (hole : hole_info) _ = n *. Int.to_float hole.fuel /. Int.to_float (hole.depth + 1)

let w_fuel n = w_fuel_base n 0.

let s rule weight =
  singleton_generator weight rule

let main : (string -> float) -> t =
  fun std_lib_m ->
  [
    var_steps                       ( w_const 2.        );
    resolve_ty_var_steps            ( w_const 2.        );
    std_lib_steps std_lib_m         ( w_const 1.        );
    lambda_steps                    ( w_fuel_base 2. 5. );
    ext_lambda_steps                ( w_fuel_base 4. 5. );
    not_useless_steps               ( w_fuel_base 2. 1. );
    let_insertion_steps             ( w_fuel_depth 1.   );
    palka_rule_steps                ( w_fuel 2.         );
    std_lib_palka_rule_steps        ( w_fuel 1.         );
    s Rules.ext_function_call_step  ( w_fuel 1.         );
    (* s Rules.function_call_step      ( w_fuel 1.         );*)
  ]

(* TODO: add a temperature that varies weights *)
