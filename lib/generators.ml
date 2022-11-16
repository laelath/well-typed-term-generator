
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
                match prog.get_ty lst_ty with
                | TyNdList ty' -> [(fst, ty'); (rst, lst_ty)]
                | _ -> raise (Util.InternalError "match scrutinee does not have list type")
           else []
         | Lambda (params, _) ->
           (match prog.get_ty node.ty with
            | TyNdArrow (ty_params, _) -> List.combine params ty_params
            | _ -> raise (Util.InternalError "lambda does not have arrow type"))
         | ExtLambda (params, _) ->
           (match prog.get_ty node.ty with
            | TyNdArrowExt (ty_params, _) -> List.combine (prog.get_params params) (prog.get_ty_params ty_params)
            | _ -> raise (Util.InternalError "lambda does not have arrow type"))
         | _ -> [] in
      exp_binds @ find_binds ep
  in
  find_binds e

(* takes E[e] and finds all lambdas i such that E_1[lambda_i xs . E_2[e]] *)
let find_enclosing_lambdas (prog : Exp.program) (e : Exp.exp_label) : (Exp.params_label list) =
  let rec find_ext_vars ty =
    match prog.get_ty ty with
    | TyNdBool -> Exp.ExtVar.Set.empty
    | TyNdInt -> Exp.ExtVar.Set.empty
    | TyNdList ty' -> find_ext_vars ty'
    | TyNdArrow (params, ty') ->
      List.fold_left
        (fun acc ty' -> Exp.ExtVar.Set.union acc (find_ext_vars ty'))
        (find_ext_vars ty') params
    | TyNdArrowExt (params, ty') ->
      Exp.ExtVar.Set.add
        (prog.ty_params_extvar params)
        (List.fold_left
          (fun acc ty' -> Exp.ExtVar.Set.union acc (find_ext_vars ty'))
          (find_ext_vars ty')
          (prog.get_ty_params params))
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
        if not (Exp.ExtVar.Set.mem (prog.params_extvar params) extvars)
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
  match prog.get_ty ty with
  | Exp.TyNdList _ -> true
  | _ -> false



(*
  TRANSITIONS
 *)

let weight_fuel1 (hole : hole_info) = hole.fuel+1
let weight_fuel0 (hole : hole_info) = hole.fuel+0

type rule_urn = (unit -> Exp.exp_label list) Urn.t

let steps_generator (prog : Exp.program) (hole : hole_info) (acc : rule_urn)
                    (rule : Exp.program -> hole_info -> 'a -> unit -> Exp.exp_label list)
                    (weight : hole_info -> int)
                    (collection : 'a list) = 
  List.fold_left (fun acc a ->
                  Urn.insert acc (weight hole) (Urn.Value (rule prog hole a)))
             acc collection

let steps_bucket_generator (prog : Exp.program) (hole : hole_info) (acc : rule_urn)
                           (rule : Exp.program -> hole_info -> 'a -> unit -> Exp.exp_label list)
                           (weight : hole_info -> int)
                           (collection : 'a list) 
                           (w : int) = 
  let nested = fun () -> steps_generator prog hole Urn.empty rule weight collection in
  Urn.insert acc w (Urn.Nested nested)

let singleton_generator weight f prog hole acc =
  Urn.insert acc (weight hole) (Urn.Value (f prog hole))



let not_useless_steps (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let params = find_enclosing_lambdas prog hole.label in
  steps_generator prog hole acc
                  Rules.not_useless_step weight_fuel1 params

let palka_rule_steps (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let funcs = List.filter (fun b -> Exp.is_func_producing prog hole.ty_label (snd b)) hole.vars in
  steps_generator prog hole acc
                  Rules.palka_rule_step weight_fuel0 funcs

let let_insertion_steps (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let weight (hole : hole_info) = max 0 (hole.fuel - hole.depth) in
  steps_generator prog hole acc
                  Rules.let_insertion_step weight (List.init (hole.depth + 1) (fun x -> x))

let match_insertion_steps (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let weight (hole : hole_info) = max 0 (hole.fuel - hole.depth) in
  let all_depths = List.init (hole.depth + 1) (fun x -> x) in
  let acc = steps_generator prog hole acc
                            Rules.match_insertion_step weight all_depths in
  match prog.get_ty hole.ty_label with
  | TyNdList _ -> 
     steps_generator prog hole acc
                     Rules.match_insertion_list_step weight all_depths
  | _ -> acc


let create_match_steps (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let lists = List.filter (fun b -> is_list_ty prog (snd b)) hole.vars in
  steps_generator prog hole acc
                  Rules.create_match_step weight_fuel0 lists 

let var_steps (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let weight _ = 1 in
  let ref_vars = List.filter (fun b -> Exp.is_same_ty prog (snd b) hole.ty_label) hole.vars in
  steps_generator prog hole acc
                  Rules.var_step weight ref_vars 


(* std_lib objects specify an occurence amount,
   objects are filtered so they can be selected 1/n of the time they are valid choices *)
let find_std_lib_refs prog tyl =
  List.filter_map
    (fun (x, (ty, n)) ->
       if Random.int n <> 0
       then None
       else Option.map (fun _ -> x) (Exp.ty_compat_ty_label prog ty tyl []))
    prog.std_lib

let std_lib_steps (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let valid_refs = find_std_lib_refs prog hole.ty_label in
  (* TODO: incorporate occurence amount here *)
  let weight _ = 1 in
  steps_generator prog hole acc
                  Rules.std_lib_step weight valid_refs

(* finds all functions in the standard library that can produce tyl *)
let find_std_lib_funcs prog tyl =
  List.filter_map
    (fun (x, (ty, n)) ->
       if Random.int n <> 0
       then None
       else match ty with
            | Exp.TyArrow (tys, ty') ->
              (match Exp.ty_compat_ty_label prog ty' tyl [] with
               | None -> None
               | Some mp -> Some (x, tys, mp))
            | _ -> None)
    prog.std_lib


let std_lib_palka_rule_steps (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let valid_refs = find_std_lib_funcs prog hole.ty_label in
  (* TODO: incorporate occurence amount here *)
  steps_generator prog hole acc
                  Rules.std_lib_palka_rule_step weight_fuel0 valid_refs

(* Implements the rule:
   E[<>] ~> E[dcon <> ... <>]
 *)
(* FIXME factor this *)
let constructor_steps (prog : Exp.program) (hole : hole_info) (acc : rule_urn) =
  let set exp =
    prog.set_exp hole.label {exp=exp; ty=hole.ty_label; prev=hole.prev}
  in

  let const_set exp msg acc =
    Urn.insert acc 1 (Urn.Value (fun () -> Printf.eprintf ("creating %s\n") msg; set exp; [])) in

  match prog.get_ty hole.ty_label with
  | TyNdBool ->
     let acc = const_set (Exp.ValBool true) "true" acc in
     let acc = const_set (Exp.ValBool false) "false" acc in
     acc
  | TyNdInt -> List.fold_left (fun acc n -> const_set (Exp.ValInt n) (Int.to_string n) acc)
                              acc (List.init 5 (fun n -> n))
  | TyNdList ty' ->
     let acc = const_set Exp.Empty "empty" acc in
     let cons = 
       fun () ->
       Printf.eprintf ("creating cons\n");
       let lhole = prog.new_exp {exp=Exp.Hole; ty=hole.ty_label; prev=Some hole.label} in
       let ehole = prog.new_exp {exp=Exp.Hole; ty=ty'; prev=Some hole.label} in
       set (Exp.Cons (ehole, lhole));
       [ehole; lhole] in
     Urn.insert acc hole.fuel (Urn.Value cons)
  | TyNdArrow (ty_params, ty') ->
     let func = 
       fun () ->
       Printf.eprintf ("creating lambda\n");
       let xs = List.map (fun _ -> prog.new_var ()) ty_params in
       let body = prog.new_exp {exp=Exp.Hole; ty=ty'; prev=Some hole.label} in
       set (Exp.Lambda (xs, body));
       [body] in
     Urn.insert acc (1 + hole.fuel) (Urn.Value func)
  | TyNdArrowExt (ty_params, ty') ->
     let func = 
       fun () ->
       Printf.eprintf ("creating ext. lambda\n");
       let extvar = prog.ty_params_extvar ty_params in
       let params = prog.new_params extvar in
       let xs = List.map (fun _ -> prog.new_var ()) (prog.get_ty_params ty_params) in
       List.iter (prog.add_param params) xs;
       let body = prog.new_exp {exp=Exp.Hole; ty=ty'; prev=Some hole.label} in
       set (Exp.ExtLambda (params, body));
       [body] in
     Urn.insert acc (1 + hole.fuel) (Urn.Value func)


type t = ((Exp.program -> hole_info -> rule_urn -> rule_urn) list)

let main : t =
  [
    constructor_steps;
    var_steps;
    std_lib_steps;
    std_lib_palka_rule_steps;
    singleton_generator weight_fuel0 Rules.ext_function_call_steps;
    let_insertion_steps;
    match_insertion_steps;
    create_match_steps;
    singleton_generator weight_fuel0 Rules.create_if_steps;
    palka_rule_steps;
    not_useless_steps;
  ]
