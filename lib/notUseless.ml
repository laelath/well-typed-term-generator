(* Each node has a unique label, which cannot be changed.
   if we have some node (call e1_l1 e2_l2) and we are updating e1 to (let (x rhs) e1),
   it's tempting to overwrite the l1 label to point to this new node.
   The problem is that we have update maps `type extension var -> program location set`
   that point to where syntactic updates need to happen, and we don't want to update these.

   Each node also has a `prev` pointer, so there's no term sharing
   allowed; each node has exactly one reference.
 *)

type worklist = {
    pop : unit -> Exp.exp_label option;
    add : int * Exp.exp_label-> unit;
  }
type state = {
    worklist : worklist;
    mutable fuel : int;
  }

type hole_info = Rules.hole_info

let make_state (fuel : int) : state =
  let holes = ref [] in
  let pop () =
    match !holes with
    | [] -> None
    | h ->
       let (hole, holes') = Choose.choose_frequency_split h in
       holes := holes';
       Some hole in
  let add e = holes := e :: !holes in
  {
    fuel = fuel;
    worklist = {
      pop = pop;
      add = add
    }
  }


exception InternalError of string

(*
  UTIL
 *)


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
                | _ -> raise (InternalError "match scrutinee does not have list type")
           else []
         | Lambda (params, _) ->
           (match prog.get_ty node.ty with
            | TyNdArrow (ty_params, _) -> List.combine params ty_params
            | _ -> raise (InternalError "lambda does not have arrow type"))
         | ExtLambda (params, _) ->
           (match prog.get_ty node.ty with
            | TyNdArrowExt (ty_params, _) -> List.combine (prog.get_params params) (prog.get_ty_params ty_params)
            | _ -> raise (InternalError "lambda does not have arrow type"))
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

let not_useless_steps (prog : Exp.program) (hole : hole_info) =
  let params = find_enclosing_lambdas prog hole.label in
  List.map (Rules.not_useless_step prog hole weight_fuel1)
           params

let palka_rule_steps (prog : Exp.program) (hole : hole_info) =
  let funcs = List.filter (fun b -> Exp.is_func_producing prog hole.ty_label (snd b)) hole.vars in
  List.map (Rules.palka_rule_step prog hole weight_fuel0)
           funcs

let let_insertion_steps (prog : Exp.program) (hole : hole_info) =
  let weight (hole : hole_info) = max 0 (hole.fuel - hole.depth) in
  List.map (Rules.let_insertion_step prog hole weight)
           (List.init (hole.depth + 1) (fun x -> x))


let match_insertion_steps (prog : Exp.program) (hole : hole_info) =
  let weight (hole : hole_info) = max 0 (hole.fuel - hole.depth) in
  let all_depths = List.init (hole.depth + 1) (fun x -> x) in
  List.map (Rules.match_insertion_step prog hole weight) 
           all_depths
  @
  match prog.get_ty hole.ty_label with
  | TyNdList _ -> List.map (Rules.match_insertion_list_step prog hole weight)
                           all_depths
  | _ -> []


let create_match_steps (prog : Exp.program) (hole : hole_info) =
  let lists = List.filter (fun b -> is_list_ty prog (snd b)) hole.vars in
  List.map (Rules.create_match_step prog hole weight_fuel0) lists

let var_steps (prog : Exp.program) (hole : hole_info) =
  let weight _ = 1 in
  let ref_vars = List.filter (fun b -> Exp.is_same_ty prog (snd b) hole.ty_label) hole.vars in
  List.map (Rules.var_step prog hole weight) ref_vars




(* std_lib objects specify an occurence amount,
   objects are filtered so they can be selected 1/n of the time they are valid choices *)
let find_std_lib_refs prog tyl =
  List.filter_map
    (fun (x, (ty, n)) ->
       if Random.int n <> 0
       then None
       else Option.map (fun _ -> x) (Exp.ty_compat_ty_label prog ty tyl []))
    prog.std_lib

let std_lib_steps (prog : Exp.program) (hole : hole_info) =
  let valid_refs = find_std_lib_refs prog hole.ty_label in
  let weight _ = 1 in
  List.map (Rules.std_lib_step weight prog hole) valid_refs



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


let std_lib_palka_rule_steps (prog : Exp.program) (hole : hole_info) =
  List.map (Rules.std_lib_palka_rule_step weight_fuel0 prog hole)
           (find_std_lib_funcs prog hole.ty_label)

(* Implements the rule:
   E[<>] ~> E[dcon <> ... <>]
 *)
(* FIXME factor this *)
let constructor_steps (prog : Exp.program) (hole : hole_info) =
  let set exp =
    prog.set_exp hole.label {exp=exp; ty=hole.ty_label; prev=hole.prev}
  in

  let const_set exp msg =
    (1, fun () -> Printf.eprintf ("creating %s\n") msg; set exp; []) in

  match prog.get_ty hole.ty_label with
  | TyNdBool -> [const_set (Exp.ValBool true) "true"; const_set (Exp.ValBool false) "false"]
  | TyNdInt -> List.init 5 (fun n -> const_set (Exp.ValInt n) (Int.to_string n))
  | TyNdList ty' ->
    [const_set Exp.Empty "empty";
     (hole.fuel,
      fun () ->
        Printf.eprintf ("creating cons\n");
        let lhole = prog.new_exp {exp=Exp.Hole; ty=hole.ty_label; prev=Some hole.label} in
        let ehole = prog.new_exp {exp=Exp.Hole; ty=ty'; prev=Some hole.label} in
        set (Exp.Cons (ehole, lhole));
        [ehole; lhole])]
  | TyNdArrow (ty_params, ty') ->
    [(1 + hole.fuel,
      fun () ->
        Printf.eprintf ("creating lambda\n");
        let xs = List.map (fun _ -> prog.new_var ()) ty_params in
        let body = prog.new_exp {exp=Exp.Hole; ty=ty'; prev=Some hole.label} in
        set (Exp.Lambda (xs, body));
        [body])]
  | TyNdArrowExt (ty_params, ty') ->
    [(1 + hole.fuel,
      fun () ->
        Printf.eprintf ("creating ext. lambda\n");
        let extvar = prog.ty_params_extvar ty_params in
        let params = prog.new_params extvar in
        let xs = List.map (fun _ -> prog.new_var ()) (prog.get_ty_params ty_params) in
        List.iter (prog.add_param params) xs;
        let body = prog.new_exp {exp=Exp.Hole; ty=ty'; prev=Some hole.label} in
        set (Exp.ExtLambda (params, body));
        [body])]


(*
   MAIN LOOP
 *)

let singleton f prog hole = [f prog hole]

let not_use_for_base (hole : hole_info) = if hole.fuel = 0 then 0 else 1

let step_generators : (Exp.program -> hole_info -> (int * (unit -> Exp.exp_label list)) list) list =
  [
    constructor_steps;
    var_steps;
    std_lib_steps;
    std_lib_palka_rule_steps;
    singleton (Rules.ext_function_call_steps weight_fuel0);
    let_insertion_steps;
    match_insertion_steps;
    create_match_steps;
    singleton (Rules.create_if_steps weight_fuel0);
    palka_rule_steps;
    not_useless_steps;
  ]

let assert_hole (exp : Exp.exp) =
  match exp with
  | Exp.Hole -> ()
  | _ -> raise (InternalError "exp is not a hole")

let sample n = Random.int n

let generate_exp (fuel : int) (prog : Exp.program) (e : Exp.exp_label) =
  let node = prog.get_exp e in
  assert_hole node.exp;
  let hole : hole_info = {
    label=e;
    ty_label=node.ty;
    prev=node.prev;
    fuel=fuel;
    vars=find_vars prog e;
    depth=exp_depth prog e;
  } in
  let steps = List.concat_map (fun g -> g prog hole) step_generators in
  (* (Urn.sample sample steps) () *)
  (Choose.choose_frequency steps) ()

let generate (st : state) (prog : Exp.program) : bool =
  match st.worklist.pop () with
  | None -> false
  | Some e ->
    let holes = generate_exp st.fuel prog e in
    List.iter (fun hole -> st.worklist.add (st.fuel + 1, hole)) holes;
    Exp.check prog;
    st.fuel <- if st.fuel > 0 then st.fuel - 1 else 0;
    true

let generate_fp ?(std_lib = []) (size : int) (ty : Exp.ty) : Exp.program =
  let prog = Exp.make_program ~std_lib: std_lib ty in
  let st = make_state size in
  st.worklist.add (st.fuel, prog.head);
  let rec lp () =
    match generate st prog with
    | false -> prog
    | true -> lp() in
  lp()
