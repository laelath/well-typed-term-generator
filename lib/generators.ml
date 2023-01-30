
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
    | TyBool -> Type.ExtVar.Set.empty
    | TyInt -> Type.ExtVar.Set.empty
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



(*
  TRANSITIONS
 *)

type rule_urn = (unit -> Exp.exp_label list) Urn.t

let steps_generator (prog : Exp.program) (hole : hole_info) (acc : rule_urn)
                    (rule : Exp.program -> hole_info -> 'a -> unit -> Exp.exp_label list)
                    (weight : hole_info -> int)
                    (collection : 'a list) = 
  List.fold_left (fun acc a ->
                  Urn.insert acc (weight hole) (Urn.Value (rule prog hole a)))
             acc collection

let bucket (bucket_weight : hole_info -> int) steps (weight : hole_info -> int) (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let nested = fun () -> steps weight prog hole acc in
  Urn.insert acc (bucket_weight hole) (Urn.Nested nested)

let singleton_generator weight f prog hole acc =
  Urn.insert acc (weight hole) (Urn.Value (f prog hole))



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



(* Palka random type function *)
module SS = Set.Make(String)

let ty_vars (t : Type.flat_ty) =
  let rec lp (t : Type.flat_ty) =
    match t with
    | FlatTyVar x -> SS.singleton x
    | FlatTyBool | FlatTyInt -> SS.empty
    | FlatTyList t' -> lp t'
    | FlatTyArrow (ts, t') -> List.fold_left SS.union (lp t') (List.map lp ts) in
  SS.elements (lp t)

let type_size_flat =
  let rec lp (t : Type.flat_ty) =
    match t with
    | FlatTyVar _ -> 1
    | FlatTyBool | FlatTyInt | FlatTyList _ -> 1
    | FlatTyArrow (params, res) -> List.fold_left (+) (1 + lp res) (List.map lp params) in
  lp

let type_size_lbl (prog : Exp.program) =
  let rec lp tyl =
    match prog.ty.get_ty tyl with
    | TyBool | TyInt | TyList _ -> 1
    | TyArrow (params, res) -> List.fold_left (+) (1 + lp res) (List.map lp params)
    | TyArrowExt (params, res) ->
      List.fold_left (+) (1 + lp res) (List.map lp (prog.ty.get_ty_params params)) in
  lp

let type_size_palka (prog : Exp.program) t =
  match t with
  | Either.Left fty -> type_size_flat fty
  | Either.Right tyl -> type_size_lbl prog tyl

let is_mono_type t =
  match t with
  | Either.Right _ -> true
  | Either.Left fty -> ty_vars fty == []

let flat_ty_to_ty_with_mapping (prog : Exp.program) m =
  let rec lp fty =
  match fty with
    | Type.FlatTyVar x -> List.assoc x m
    | Type.FlatTyBool -> prog.ty.new_ty Type.TyBool
    | Type.FlatTyInt -> prog.ty.new_ty Type.TyInt
    | Type.FlatTyList fty' -> prog.ty.new_ty (Type.TyList (lp fty'))
    | Type.FlatTyArrow (params, res) -> prog.ty.new_ty (TyArrow (List.rev_map lp params, lp res)) in
  lp

(* NOTE: using the fact that all the tys in tyls are monomorphic *)
(* Uses all the types in the standard library by default,
   the type labels from the context will need to be harvested by the generator that uses this. *)
let random_type_palka (prog : Exp.program) (n0 : int) (tyls : Type.ty_label list) =
  let l = List.map Either.left (List.map (fun x -> fst (snd x)) prog.std_lib)
        @ List.map Either.right tyls in
  (* In the palka code this function is filling all the polymorphic type variables
     in the type with monomorphic ones *)
  let mono_types = List.filter is_mono_type l in
  let base m p =
    match p with
    | Either.Right tyl -> fun () -> tyl
    | Either.Left fty ->
      (* If it's a flat ty we need to instantiate all the type variables *)
      fun () ->
        let tvars = ty_vars fty in
        let ty_choices = List.filter (fun x -> type_size_palka prog x < m * 2 + 4) mono_types in
        let ty_args = List.init (List.length tvars)
                                (fun _ -> match (Choose.choose ty_choices) with
                                 | Either.Left fty -> prog.ty.flat_ty_to_ty fty
                                 | Either.Right tyl -> tyl) in
        flat_ty_to_ty_with_mapping prog (List.combine tvars ty_args) fty
    in
  let rec aux n =
    let weight_filter w f =
      let l' = List.filter f l in
      if l' == []
      then []
      else [(w, (fun () -> Choose.choose (List.map (base n) l') ()))] in
    (Choose.choose_frequency
       (weight_filter 4 (fun x -> type_size_palka prog x < 3) @
        weight_filter 4 (fun x -> type_size_palka prog x < n + 2) @
        weight_filter 2 (fun x -> type_size_palka prog x < n * 2 + 8) @
        (if n > 3
         then [(1, fun () -> prog.ty.new_ty (Type.TyArrow ([aux (n / 2)], aux (n / 2))))]
         else []))) () in
  aux n0



let create_match_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let lists = List.filter (fun b -> is_list_ty prog (snd b)) hole.vars in
  steps_generator prog hole acc
                  Rules.create_match_step weight lists

let var_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let ref_vars = List.filter (fun b -> Type.is_same_ty prog.ty (snd b) hole.ty_label) hole.vars in
  steps_generator prog hole acc
                  Rules.var_step weight ref_vars


(* std_lib objects specify an occurence amount,
   objects are filtered so they can be selected 1/n of the time they are valid choices *)
let find_std_lib_refs (prog : Exp.program) tyl =
  List.filter_map
    (fun (x, (ty, n)) ->
       if Random.int n <> 0
       then None
       else Option.map (fun _ -> x) (Type.ty_compat_ty_label prog.ty ty tyl []))
    prog.std_lib

let std_lib_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let valid_refs = find_std_lib_refs prog hole.ty_label in
  (* TODO: incorporate occurence amount here *)
  steps_generator prog hole acc
                  Rules.std_lib_step weight valid_refs

(* finds all functions in the standard library that can produce tyl *)
let find_std_lib_funcs (prog : Exp.program) tyl =
  List.filter_map
    (fun (x, (ty, n)) ->
       if Random.int n <> 0
       then None
       else match ty with
            | Type.FlatTyArrow (tys, ty') ->
              (match Type.ty_compat_ty_label prog.ty ty' tyl [] with
               | None -> None
               | Some mp -> Some (x, tys, mp))
            | _ -> None)
    prog.std_lib


let std_lib_palka_rule_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let valid_refs = find_std_lib_funcs prog hole.ty_label in
  (* TODO: incorporate occurence amount here *)
  steps_generator prog hole acc
                  Rules.std_lib_palka_rule_step weight valid_refs


let base_constructor_steps weight (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  (* TODO: sample base type (in this case, just Int) *)
  match  prog.ty.get_ty hole.ty_label with
  | TyInt ->
     let vals = [Exp.ValInt 0; Exp.ValInt 1; Exp.ValInt 33] in
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

type t = ((Exp.program -> hole_info -> rule_urn -> rule_urn) list)

let c (w : int) (_ : hole_info) = w
let w_const = c 1
let w_fuel (hole : hole_info) = hole.fuel+1
let w_fuel_depth (hole : hole_info) = max 1 (hole.fuel - hole.depth)

let not_base weight (hole : hole_info) =
  if hole.fuel = 0
  then 0
  else weight hole

let s rule weight =
  singleton_generator weight rule

let main : t =
  [
    (* RULE TYPE *)                     (* IS BASE CASE? *)   (* WEIGHT *)
    base_constructor_steps             (                        w_const          );
    data_constructor_steps             (                        w_const          );
    func_constructor_steps             (                        w_fuel           );
    var_steps                          (                        w_const          );
    (* --------------------------------------------------------------------------*)
    std_lib_steps                      (                        w_const          );
    std_lib_palka_rule_steps           (     not_base           w_fuel           );
    (* --------------------------------------------------------------------------*)
    s Rules.ext_function_call_step     (     not_base           w_fuel           );
    (* --------------------------------------------------------------------------*)
    let_insertion_steps                (     not_base           w_fuel_depth     );
    (* --------------------------------------------------------------------------*)
    match_insertion_steps              (     not_base           w_fuel_depth     );
    create_match_steps                 (     not_base           w_fuel           );
    (* --------------------------------------------------------------------------*)
    s Rules.create_if_step             (     not_base           w_fuel           );
    (* --------------------------------------------------------------------------*)
    palka_rule_steps                   (     not_base           w_fuel           );
    (* --------------------------------------------------------------------------*)
    not_useless_steps                  (                        w_fuel           );
  ]


(* NOTES ABOUT THE BELOW: variables can come from the program context (lexical scope) or from the global environment *)

(* fills the hole with a monomorphic variable of the same type *)
let mono_var_steps _weight (_prog : Exp.program) (_hole : hole_info) (_acc : rule_urn) =
  raise Util.Unimplemented

  (* fills the hole with a polymorphic variable that completely matches the type (no free type variables after unification *)
let poly_var_steps _weight (_prog : Exp.program) (_hole : hole_info) (_acc : rule_urn) =
  raise Util.Unimplemented

(* fills the hole with a function application where the function is a monomorphic variable *)
let mono_palka_func_steps _weight (_prog : Exp.program) (_hole : hole_info) (_acc : rule_urn) =
  raise Util.Unimplemented

(* fills the hole with a function application where the function is a polymorphic variable that completely matches *)
let poly_palka_func_steps _weight (_prog : Exp.program) (_hole : hole_info) (_acc : rule_urn) =
  raise Util.Unimplemented

(* fills the hole with a function application where the function is a polymorphic variable that doesn't completely match. A random type is chosen for all free type variables *)
let poly_palka_func_steps' _weight (_prog : Exp.program) (_hole : hole_info) (_acc : rule_urn) =
  raise Util.Unimplemented

(* fills the hole with a function application where the function is a hole and the input type is random *)
let application_steps _weight (_prog : Exp.program) (_hole : hole_info) (_acc : rule_urn) =
  raise Util.Unimplemented

(* fills the hole with a seq where the lhs is a variable *)
let palka_seq_steps _weight (_prog : Exp.program) (_hole : hole_info) (_acc : rule_urn) =
  raise Util.Unimplemented

let not_palka_base weight (hole : hole_info) =
  if raise Util.Unimplemented
 (* palkaTypeSize hole.ty_label > hole.fuel + 15 *)
  then 0
  else weight hole

(* TODO: fix weights on these. I think the palka termination condition is 
   typeSize t > size + 15 ---> do base case only
*)

let palka : t = 
  [
    (* TODO: base case *)
    (* bucket    ?    ...                        (                 w_const) *)
    bucket    (c 4)    mono_var_steps            (not_palka_base    w_const);
    bucket    (c 2)    poly_var_steps            (not_palka_base    w_const);
    bucket    (c 4)    mono_palka_func_steps     (not_palka_base    w_const);
    bucket    (c 2)    poly_palka_func_steps     (not_palka_base    w_const);
    bucket    (c 2)    poly_palka_func_steps'    (not_palka_base    w_const);
    bucket    (c 8)    func_constructor_steps    (not_palka_base    w_const);
    bucket    (c 8)    application_steps         (not_palka_base    w_const);
    bucket    (c 6)    palka_seq_steps           (not_palka_base    w_const);
  ]


