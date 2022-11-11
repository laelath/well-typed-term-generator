(* Each node has a unique label, which cannot be changed.
   if we have some node (call e1_l1 e2_l2) and we are updating e1 to (let (x rhs) e1),
   it's tempting to overwrite the l1 label to point to this new node.
   The problem is that we have update maps `type extension var -> program location set`
   that point to where syntactic updates need to happen, and we don't want to update these.

   Each node also has a `prev` pointer, so there's no term sharing
   allowed; each node has exactly one reference.
 *)

let choose (lst : 'a list) : 'a =
  let i = Random.int (List.length lst) in
  List.nth lst i

let choose_split (lst : 'a list) : 'a * ('a list) =
  let rec extract i lst =
    let hd = List.hd lst in
    if i == 0
    then (hd, List.tl lst)
    else let (a, lst') = extract (i - 1) (List.tl lst) in
         (a, hd :: lst') in
  extract (Random.int (List.length lst)) lst

let choose_frequency (freqs : (int * 'a) list) : 'a =
  let rec get_freq (freqs : (int * 'a) list) (i : int) : 'a =
    let (n, a) = List.hd freqs in
    if i < n
    then a
    else get_freq (List.tl freqs) (i - n) in

  let n = List.fold_left (fun acc (m, _) -> acc + m) 0 freqs in
  get_freq freqs (Random.int n)

let choose_frequency_split (freqs : (int * 'a) list) : 'a * ((int * 'a) list) =
  let rec extract_freq i lst =
    let hd = List.hd lst in
    if i < fst hd
    then (snd hd, List.tl lst)
    else let (a, lst') = extract_freq (i - fst hd) (List.tl lst) in
         (a, hd :: lst') in
  let n = List.fold_left (fun acc (m, _) -> acc + m) 0 freqs in
  extract_freq (Random.int n) freqs

type worklist = {
    pop : unit -> Exp.exp_label option;
    add : int * Exp.exp_label-> unit;
  }
type state = {
    worklist : worklist;
    mutable size : int;
  }
type hole_info = {
    label : Exp.exp_label;
    ty_label : Exp.ty_label;
    prev : Exp.exp_label option;
    fuel : int;
    vars : (Exp.var * Exp.ty_label) list;
    depth : int;
  }

let make_state (size : int) : state =
  let holes = ref [] in
  let pop () =
    if List.length !holes == 0
    then None
    else let (hole, holes') = choose_frequency_split !holes in
         holes := holes';
         Some hole in
  {
    size = size;
    worklist = {
      pop = pop;
      add = fun e -> holes := e :: !holes
    }
  }


exception InternalError of string


(* Implements the rule:
   E ~> E{alpha + tau}
 *)
let extend_extvar (prog : Exp.program) (extvar : Exp.extvar) (ext_ty : Exp.ty_label) =
  let extend : 'a 'b . Exp.extvar -> (Exp.extvar -> 'a list) -> ('a -> unit) -> unit =
    fun ext get add ->
    let lst = get ext in
    let handle_elt elt = add elt in
    List.iter handle_elt lst in

  extend extvar prog.extvar_ty_params
         (fun ty_params -> prog.add_ty_param ty_params ext_ty);
  extend extvar prog.extvar_params
         (fun param -> prog.add_param param (prog.new_var()));

  (* Justin: there has to be a better way... *)
  (* Ben: no *)
  let exp_lbls = ref [] in
  extend extvar prog.extvar_args
         (fun arg ->
          let app_lbl = prog.args_parent arg in
          let exp_lbl = prog.new_exp {exp=Exp.Hole; ty=ext_ty; prev=Some app_lbl} in
          prog.add_arg arg exp_lbl;
          exp_lbls := exp_lbl :: !exp_lbls);

  !exp_lbls

(* finds all the variables in scope of a hole *)
let find_vars (prog : Exp.program) (e : Exp.exp_label) =
  let rec find_binds (e : Exp.exp_label) =
    match (prog.get_exp e).prev with
    | None -> []
    | Some ep ->
      let node = prog.get_exp ep in
      List.append
        (match node.exp with
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
         | _ -> [])
        (find_binds ep) in
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


(*
  TRANSITIONS
 *)

(* Implements the rule:
   E_1[lambda_i xs alpha . E_2[<>]] ~>
   E_1{alpha + tau}[lambda_i (x::xs) alpha . E_2{alpha + tau}[x]]

   via the decomposition

   E_1[lambda_i xs alpha . E_2[<>]] ~>
   E_1{alpha + tau}[lambda_i (x::xs) alpha . E_2{alpha+tau}[<>]] ~>
   E_1{alpha + tau}[lambda_i (x::xs) alpha . E_2{alpha + tau}[x]]
 *)
let not_useless_steps (prog : Exp.program) (hole : hole_info) =
  let not_useless_step param =
    (hole.fuel + 1,
     fun () ->
       Printf.eprintf ("extending ext. var\n");
       let extvar = prog.params_extvar param in
       let holes = extend_extvar prog extvar hole.ty_label in
       let x = List.hd (prog.get_params param) in
       prog.set_exp hole.label {exp=Exp.Var x; ty=hole.ty_label; prev=hole.prev};
       holes)
  in

  let params = find_enclosing_lambdas prog hole.label in
  List.map not_useless_step params

(* Implements the rule:
   E[<>] ~> E[call <> alpha] where alpha is fresh
 *)
let ext_function_call_steps (prog : Exp.program) (hole : hole_info) =
  [(hole.fuel,
    fun () ->
      Printf.eprintf ("creating ext. function call\n");
      let extvar = prog.new_extvar() in
      let f_ty = prog.new_ty (Exp.TyNdArrowExt (prog.new_ty_params extvar, hole.ty_label)) in
      let f = prog.new_exp {exp=Exp.Hole; ty=f_ty; prev=Some hole.label} in
      let args = prog.new_args extvar hole.label in
      prog.set_exp hole.label {exp=Exp.ExtCall (f, args); ty=hole.ty_label; prev=hole.prev};
      [f])]

(* Implements the rule:
   E[<>] ~> E[call f <> ... alpha] where f is in alpha
 *)
let palka_rule_steps (prog : Exp.program) (hole : hole_info) =
  let palka_rule_step (f, f_ty) =
    (hole.fuel,
     fun () ->
       Printf.eprintf ("creating palka function call\n");
       let fe = prog.new_exp {exp=Exp.Var f; ty=f_ty; prev=Some hole.label} in
       match (prog.get_ty f_ty) with
       | Exp.TyNdArrowExt (ty_params, _) ->
         let extvar = prog.ty_params_extvar ty_params in
         let args = prog.new_args extvar hole.label in
         let holes = List.map (fun arg_ty ->
                                 let hole = prog.new_exp {exp=Exp.Hole; ty=arg_ty; prev=Some hole.label} in
                                 prog.add_arg args hole;
                                 hole)
                              (List.rev (prog.get_ty_params ty_params)) in
         prog.set_exp hole.label {exp=Exp.ExtCall (fe, args); ty=hole.ty_label; prev=hole.prev};
         holes
       | Exp.TyNdArrow (tys, _) ->
         let holes = List.map (fun arg_ty -> prog.new_exp {exp=Exp.Hole; ty=arg_ty; prev=Some hole.label}) tys in
         prog.set_exp hole.label {exp=Exp.Call (fe, holes); ty=hole.ty_label; prev=hole.prev};
         holes
       | _ -> raise (InternalError "variable in function list not a function"))
  in

  let funcs = List.filter (fun b -> Exp.is_func_producing prog hole.ty_label (snd b)) hole.vars in
  List.map palka_rule_step funcs


let exp_depth (prog : Exp.program) (e : Exp.exp_label) =
  let rec exp_depth' e acc =
    let node = prog.get_exp e in
    match node.prev with
    | None -> acc
    | Some e' -> exp_depth' e' (acc + 1) in
  exp_depth' e 0

let rec find_pos (prog : Exp.program) (e : Exp.exp_label) (height : int) =
  if height == 0
  then e
  else match (prog.get_exp e).prev with
       | None -> e
       | Some e' -> find_pos prog e' (height - 1)

let let_insertion_steps (prog : Exp.program) (hole : hole_info) =
  let let_insertion_step height =
    (max 0 (hole.fuel - hole.depth),
     fun () ->
       Printf.eprintf ("inserting let\n");
       let e' = find_pos prog hole.label height in
       let node' = prog.get_exp e' in
       let x = prog.new_var () in
       let e_let = prog.new_exp {exp=Exp.Hole; ty=node'.ty; prev=node'.prev} in
       let e_hole = prog.new_exp {exp=Exp.Hole; ty=hole.ty_label; prev=Some e_let} in
       prog.set_exp e_let {exp=Exp.Let (x, e_hole, e'); ty=node'.ty; prev=node'.prev};
       prog.set_exp e' {exp=node'.exp; ty=node'.ty; prev=Some e_let};
       (match node'.prev with
        | None -> prog.head <- e_let
        | Some e'' -> prog.rename_child (e', e_let) e'');
       let node = prog.get_exp hole.label in
       prog.set_exp hole.label {exp=Exp.Var x; ty=node.ty; prev=node.prev};
       [e_hole])
  in
  List.map let_insertion_step (List.init (hole.depth + 1) (fun x -> x))


(* TODO: flatten choice of adding it as list binding *)
let match_insertion_steps (prog : Exp.program) (hole : hole_info) =
  let match_insertion_step height =
    (max 0 (hole.fuel - hole.depth),
     fun () ->
       Printf.eprintf ("inserting match\n");
       let e' = find_pos prog hole.label height in
       let node' = prog.get_exp e' in
       let e_match = prog.new_exp {exp=Exp.Hole; ty=node'.ty; prev=node'.prev} in
       let hole_nil = prog.new_exp {exp=Exp.Hole; ty=node'.ty; prev=Some e_match} in
       let list_ty = match (prog.get_ty hole.ty_label, choose_frequency [(3, true); (1, false)]) with
                     | TyNdList _, true -> Either.Left hole.ty_label
                     | _ -> Either.Right (prog.new_ty (Exp.TyNdList hole.ty_label)) in
       let hole_scr = prog.new_exp {exp=Exp.Hole; ty=(match list_ty with | Left ty' -> ty' | Right ty' -> ty'); prev=Some e_match} in
       let x = prog.new_var () in
       let y = prog.new_var () in
       prog.set_exp e_match {exp=Exp.Match (hole_scr, hole_nil, (x, y, e')); ty=node'.ty; prev=node'.prev};
       prog.set_exp e' {exp=node'.exp; ty=node'.ty; prev=Some e_match};
       (match node'.prev with
        | None -> prog.head <- e_match
        | Some e'' -> prog.rename_child (e', e_match) e'');
       let node = prog.get_exp hole.label in
       prog.set_exp hole.label {exp=Exp.Var (match list_ty with | Left _ -> y | Right _ -> x); ty=node.ty; prev=node.prev};
       [hole_scr; hole_nil])
  in
  List.map match_insertion_step (List.init (hole.depth + 1) (fun x -> x))


let is_list_ty (prog : Exp.program) ty =
  match prog.get_ty ty with
  | Exp.TyNdList _ -> true
  | _ -> false

let create_match_steps (prog : Exp.program) (hole : hole_info) =
  let create_match_step (x, ty) =
    (hole.fuel,
     fun () ->
       Printf.eprintf ("creating match\n");
       let e_scr = prog.new_exp {exp=Exp.Var x; ty=ty; prev=Some hole.label} in
       let e_empty = prog.new_exp {exp=Exp.Hole; ty=hole.ty_label; prev=Some hole.label} in
       let e_cons = prog.new_exp {exp=Exp.Hole; ty=hole.ty_label; prev=Some hole.label} in
       prog.set_exp hole.label
                    {exp=Exp.Match (e_scr, e_empty, (prog.new_var (), prog.new_var (), e_cons));
                     ty=hole.ty_label; prev=hole.prev};
       [e_empty; e_cons])
  in
  let lists = List.filter (fun b -> is_list_ty prog (snd b)) hole.vars in
  List.map create_match_step lists


(* Implements the rule:
   E[<>] ~> E[x]
 *)
(* TODO: increase the chance of variable reference for complex types? *)
let var_steps (prog : Exp.program) (hole : hole_info) =
  let var_step (var, _) =
    (1, fun () ->
          Printf.eprintf ("creating var reference\n");
          prog.set_exp hole.label {exp=Exp.Var var; ty=hole.ty_label; prev=hole.prev};
          [])
  in

  let ref_vars = List.filter (fun b -> Exp.is_same_ty prog (snd b) hole.ty_label) hole.vars in
  List.map var_step ref_vars


(* Implements the rule *)
let create_if_steps (prog : Exp.program) (hole : hole_info) =
  [(hole.fuel,
    fun () ->
      Printf.eprintf ("creating if\n");
      let pred = prog.new_exp {exp=Exp.Hole; ty=prog.new_ty Exp.TyNdBool; prev=Some hole.label} in
      let thn = prog.new_exp {exp=Exp.Hole; ty=hole.ty_label; prev=Some hole.label} in
      let els = prog.new_exp {exp=Exp.Hole; ty=hole.ty_label; prev=Some hole.label} in
      prog.set_exp hole.label {exp=Exp.If (pred, thn, els); ty=hole.ty_label; prev=hole.prev};
      [pred; thn; els])]


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
  let std_lib_step x =
    (1, (* TODO: incorporate occurence amount here *)
     fun () ->
       Printf.eprintf ("creating std lib reference: %s\n") x;
       prog.set_exp hole.label {exp=Exp.StdLibRef x; ty=hole.ty_label; prev=hole.prev};
       [])
  in
  let valid_refs = find_std_lib_refs prog hole.ty_label in
  List.map std_lib_step valid_refs


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

(* TODO: pass full list of in-scope variables here *)
let rec generate_type size (prog : Exp.program) =
  prog.new_ty
    ((choose_frequency
        [(1, (fun _ -> Exp.TyNdBool)); (1, (fun _ -> Exp.TyNdInt));
         (size, (fun _ -> Exp.TyNdList (generate_type (size - 1) prog)))])
     ())

let rec ty_label_from_ty prog mp ty =
  match ty with
  | Exp.TyVar var ->
    (match List.assoc_opt var mp with
     | None -> let tyl = generate_type 3 prog in
               ((var, tyl) :: mp, tyl)
     | Some tyl -> (mp, tyl))
  | Exp.TyInt -> (mp, prog.new_ty Exp.TyNdInt)
  | Exp.TyBool -> (mp, prog.new_ty Exp.TyNdBool)
  | Exp.TyList ty' ->
    let (mp, tyl') = ty_label_from_ty prog mp ty' in
    (mp, prog.new_ty (Exp.TyNdList tyl'))
  | Exp.TyArrow (tys, ty') ->
    let (mp, tyl') = ty_label_from_ty prog mp ty' in
    let (mp, tys') = List.fold_left_map (ty_label_from_ty prog) mp (List.rev tys) in
    (mp, prog.new_ty (Exp.TyNdArrow (tys', tyl')))

let std_lib_palka_rule_steps (prog : Exp.program) (hole : hole_info) =
  let std_lib_palka_rule_step (f, tys, mp) =
    (hole.fuel, (* TODO: incorporate occurence amount here *)
     fun () ->
       Printf.eprintf ("creating std lib palka call: %s\n") f;
       let (_, tyls) = List.fold_left_map (ty_label_from_ty prog) mp (List.rev tys) in
       let holes = List.map (fun tyl -> prog.new_exp {exp=Exp.Hole; ty=tyl; prev=Some hole.label}) tyls in
       let func = prog.new_exp {exp=Exp.StdLibRef f; ty=prog.new_ty (Exp.TyNdArrow (tyls, hole.ty_label)); prev=Some hole.label} in
       prog.set_exp hole.label {exp=Exp.Call (func, holes); ty=hole.ty_label; prev=hole.prev};
       holes)
  in
  List.map std_lib_palka_rule_step (find_std_lib_funcs prog hole.ty_label)


(* TODO: use this again *)
let rec type_complexity (prog : Exp.program) (ty : Exp.ty_label) =
  match prog.get_ty ty with
  | Exp.TyNdBool -> 1
  | Exp.TyNdInt -> 1
  | Exp.TyNdList ty' -> 2 + type_complexity prog ty'
  | Exp.TyNdArrow (params, ty') ->
    List.fold_left
      (fun acc ty'' -> acc + type_complexity prog ty'')
      (1 + type_complexity prog ty')
      params
  | Exp.TyNdArrowExt (params, ty') ->
    List.fold_left
      (fun acc ty'' -> acc + type_complexity prog ty'')
      (1 + type_complexity prog ty')
      (prog.get_ty_params params)

(* Implements the rule:
   E[<>] ~> E[dcon <> ... <>]
 *)
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

let assert_hole (exp : Exp.exp) =
  match exp with
  | Exp.Hole -> ()
  | _ -> raise (InternalError "exp is not a hole")

let step_generators : (Exp.program -> hole_info -> (int * (unit -> Exp.exp_label list)) list) list =
  [
    constructor_steps;
    var_steps;
    std_lib_steps;
    std_lib_palka_rule_steps;
    ext_function_call_steps;
    let_insertion_steps;
    match_insertion_steps;
    create_match_steps;
    create_if_steps;
    palka_rule_steps;
    not_useless_steps;
  ]

let generate_exp (fuel : int) (prog : Exp.program) (e : Exp.exp_label) =
  let node = prog.get_exp e in
  assert_hole node.exp;
  let hole = {
    label=e;
    ty_label=node.ty;
    prev=node.prev;
    fuel=fuel;
    vars=find_vars prog e;
    depth=exp_depth prog e;
  } in
  let steps = List.concat_map (fun g -> g prog hole) step_generators in
  (choose_frequency steps) ()

let generate (st : state) (prog : Exp.program) : bool =
  match st.worklist.pop () with
  | None -> false
  | Some e ->
    let holes = generate_exp st.size prog e in
    List.iter (fun hole -> st.worklist.add (st.size + 1, hole)) holes;
    Exp.check prog;
    st.size <- if st.size > 0 then st.size - 1 else 0;
    true

let generate_fp ?(std_lib = []) (size : int) (ty : Exp.ty) : Exp.program =
  let prog = Exp.make_program ~std_lib: std_lib ty in
  let st = make_state size in
  st.worklist.add (st.size, prog.head);
  let rec lp () =
    match generate st prog with
    | false -> prog
    | true -> lp() in
  lp()
