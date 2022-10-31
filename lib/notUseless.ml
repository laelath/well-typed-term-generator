
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
    if i == 0
    then (List.hd lst, List.tl lst)
    else let (a, lst') = extract (i - 1) (List.tl lst) in
         (a, List.hd lst :: lst') in
  extract (Random.int (List.length lst)) lst

let rec get_freq (freqs : (int * 'a) list) (i : int) : 'a =
  let (n, a) = List.hd freqs in
  if i < n
  then a
  else get_freq (List.tl freqs) (i-n)

let choose_frequency (freqs : (int * 'a) list) : 'a =
  let n = List.fold_left (fun acc (m, _) -> acc + m) 0 freqs in
  let i = Random.int n in
  get_freq freqs i

type worklist = {
    pop : unit -> Exp.exp_label option;
    add : Exp.exp_label -> unit;
  }
type state = {
    worklist : worklist;
    mutable size : int;
  }

let make_state (size : int) : state =
  let holes = ref [] in
  let pop () =
    if List.length !holes ==0
    then None
    else let (hole, holes') = choose_split !holes in
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

(* finds all the variables with the same type,
   functions that return this type,
   and TODO: types equivalent up to extvar extensions *)
let rec find_vars (prog : Exp.program) (e : Exp.exp_label option) (ty : Exp.ty_label) =
  match e with
  | None -> ([], [])
  | Some e ->
    let node = prog.get_exp e in
    match node.exp with
    | ExtLambda (params, _) ->
      let (vars, funcs) = find_vars prog node.prev ty in
      let ty_params = match prog.get_ty node.ty with
                      | TyArrowExt (ty_params, _) -> ty_params
                      | _ -> raise (InternalError "lambda does not have arrow type") in
      let binds = List.combine (prog.get_params params) (prog.get_ty_params ty_params) in
      let vars' = List.filter (fun b -> Exp.is_same_ty prog (snd b) ty) binds in
      let funcs' = List.filter (fun b -> Exp.is_func_producing prog (snd b) ty) binds in
      (List.append vars' vars, List.append funcs' funcs)
    | _ -> find_vars prog node.prev ty

(* takes E[e] and finds all lambdas i such that E_1[lambda_i xs . E_2[e]] *)
let rec find_enclosing_lambdas (prog : Exp.program) (e : Exp.exp_label option) acc : (Exp.params_label list) =
  match e with
  | None -> acc
  | Some e ->
    let node = prog.get_exp e in
    match node.exp with
    | ExtLambda (params, _) -> find_enclosing_lambdas prog node.prev (params :: acc)
    | _ -> find_enclosing_lambdas prog node.prev acc


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
let not_useless_rule (params : Exp.params_label list) (prog : Exp.program) (e : Exp.exp_label) =
  Printf.printf("extending ext. variable\n");
  let node = prog.get_exp e in
  (* TODO: filter params by ty, don't want to cause circularities? *)
  let param = choose params in
  let extvar = prog.params_extvar param in
  let holes = extend_extvar prog extvar node.ty in

  let x = List.hd (prog.get_params param) in
  prog.set_exp e {exp=Exp.Var x; ty=node.ty; prev=node.prev};
  holes

(* Implements the rule:
   E[<>] ~> E[call <> alpha] where alpha is fresh
 *)
let create_ext_function_call (prog : Exp.program) (e : Exp.exp_label) =
  Printf.printf("creating ext. function call\n");
  let node = prog.get_exp e in
  let extvar = prog.new_extvar() in
  let f_ty = prog.new_ty (Exp.TyArrowExt (prog.new_ty_params extvar, node.ty)) in
  let f = prog.new_exp {exp=Exp.Hole; ty=f_ty; prev=Some e} in
  let args = prog.new_args extvar e in
  prog.set_exp e {exp=Exp.ExtCall (f, args); ty=node.ty; prev=node.prev};
  [f]

(* Implements the rule:
   E[<>] ~> E[call f <> ... alpha] where f is in alpha
 *)
let palka_rule (funcs : (Exp.var * Exp.ty_label) list) (prog : Exp.program) (e : Exp.exp_label) =
  Printf.printf("creating ext. palka function call\n");
  let node = prog.get_exp e in
  let (f, f_ty) = choose funcs in
  let fe = prog.new_exp {exp=Exp.Var f; ty=f_ty; prev=Some e} in
  match (prog.get_ty f_ty) with
  | Exp.TyArrowExt (ty_params, _) ->
    let extvar = prog.ty_params_extvar ty_params in
    let args = prog.new_args extvar e in
    let holes = List.map (fun arg_ty ->
                            let hole = prog.new_exp {exp=Exp.Hole; ty=arg_ty; prev=Some e} in
                            prog.add_arg args hole;
                            hole)
                         (List.rev (prog.get_ty_params ty_params)) in
    prog.set_exp e {exp=Exp.ExtCall (fe, args); ty=node.ty; prev=node.prev};
    holes
  | Exp.TyArrow (tys, _) ->
    let holes = List.map (fun arg_ty -> prog.new_exp {exp=Exp.Hole; ty=arg_ty; prev=Some e}) tys in
    prog.set_exp e {exp=Exp.Call (fe, holes); ty=node.ty; prev=node.prev};
    holes
  | _ -> raise (InternalError "variable in function list not a function")

let exp_depth (prog : Exp.program) (e : Exp.exp_label) =
  let rec exp_depth' e acc =
    let node = prog.get_exp e in
    match node.prev with
    | None -> acc
    | Some e' -> exp_depth' e' (acc + 1) in
  exp_depth' e 0

let rec find_pos (height : int) (prog : Exp.program) (e : Exp.exp_label) =
  if height == 0
  then e
  else match (prog.get_exp e).prev with
       | None -> e
       | Some e' -> find_pos (height - 1) prog e'

let let_insertion (prog : Exp.program) (e : Exp.exp_label) =
  Printf.printf("inserting let\n");
  let ty = (prog.get_exp e).ty in
  let depth = exp_depth prog e in
  let e' = find_pos (Random.int (depth + 1)) prog e in
  let node' = prog.get_exp e' in
  let x = prog.new_var () in
  let lt = prog.new_exp {exp=Exp.Hole; ty=node'.ty; prev=node'.prev} in
  let hole = prog.new_exp {exp=Exp.Hole; ty=ty; prev=Some lt} in
  prog.set_exp lt {exp=Exp.Let (x, hole, e'); ty=node'.ty; prev=node'.prev};
  prog.set_exp e' {exp=node'.exp; ty=node'.ty; prev=Some lt};
  (match node'.prev with
   | None -> prog.head <- lt
   | Some e'' -> prog.rename_child (e', lt) e'');
  let node = prog.get_exp e in
  prog.set_exp e {exp=Exp.Var x; ty=node.ty; prev=node.prev};
  [hole]

(* Implements the rule:
   E[<>] ~> E[x]
 *)
let create_var (vars : (Exp.var * Exp.ty_label) list) (prog : Exp.program) (e : Exp.exp_label) =
  Printf.printf("creating var reference\n");
  let node = prog.get_exp e in
  prog.set_exp e {exp=Exp.Var (fst (choose vars)); ty=node.ty; prev=node.prev};
  []

(* Implements the rule *)
let create_if (prog : Exp.program) (e : Exp.exp_label) =
  Printf.printf("creating if\n");
  let node = prog.get_exp e in
  let pred = prog.new_exp {exp=Exp.Hole; ty=prog.new_ty Exp.TyBool; prev=Some e} in
  let thn = prog.new_exp {exp=Exp.Hole; ty=node.ty; prev=Some e} in
  let els = prog.new_exp {exp=Exp.Hole; ty=node.ty; prev=Some e} in
  prog.set_exp e {exp=Exp.If (pred, thn, els); ty=node.ty; prev=node.prev};
  [pred; thn; els]

(* Implements the rule:
   E[<>] ~> E[dcon <> ... <>]
 *)
let create_constructor (size : int) (prog : Exp.program) (e : Exp.exp_label) =
  Printf.printf("creating constructor\n");
  let node = prog.get_exp e in

  let create_lambda params ty_im =
    let xs = List.map (fun _ -> prog.new_var()) params in
    let body = prog.new_exp {exp=Exp.Hole; ty=ty_im; prev=Some e} in
    (Exp.Lambda (xs, body), [body])
  in

  let create_ext_lambda ty_params ty_im =
    let extvar = prog.ty_params_extvar ty_params in
    let params = prog.new_params extvar in
    let xs = List.map (fun _ -> prog.new_var()) (prog.get_ty_params ty_params) in
    List.iter (prog.add_param params) xs;
    let body = prog.new_exp {exp=Exp.Hole; ty=ty_im; prev=Some e} in
    (Exp.ExtLambda (params, body), [body])
  in

  let create_list ty' =
    if size == 0
    then (Exp.Empty, [])
    else let lhole = prog.new_exp {exp=Exp.Hole; ty=node.ty; prev=Some e} in
         let ehole = prog.new_exp {exp=Exp.Hole; ty=ty'; prev=Some e} in
         (Exp.Cons (ehole, lhole), [ehole; lhole])
  in

  let (exp, holes) = match (prog.get_ty node.ty) with
    | TyBool -> (Exp.ValBool (choose [false; true]), [])
    | TyInt -> (Exp.ValInt 0, [])
    | TyList ty' -> create_list ty'
    | TyArrow (params, ty_im) -> create_lambda params ty_im
    | TyArrowExt (ty_params, ty_im) -> create_ext_lambda ty_params ty_im in
  prog.set_exp e {exp=exp; ty=node.ty; prev=node.prev};
  holes


(*
   MAIN LOOP
 *)

let constructor_priority (size : int) (prog : Exp.program) (ty : Exp.ty_label) =
  match prog.get_ty ty with
  | Exp.TyBool -> 1
  | Exp.TyInt -> 1
  | Exp.TyList _ -> max 1 size
  | Exp.TyArrow (_, _) -> max 1 size
  | Exp.TyArrowExt (_, _) -> max 1 (size * 4)

let assert_hole (exp : Exp.exp) =
  match exp with
  | Exp.Hole -> ()
  | _ -> raise (InternalError "exp is not a hole")

(* 1. find the list of variables that can be referenced
   2. find the list of binding locations
   3. choose between a variable reference, an application, an if, or a constructor *)

let generate_exp (size : int) (prog : Exp.program) (e : Exp.exp_label) =
  let node = prog.get_exp e in
  assert_hole node.exp;
  let vars, funcs = find_vars prog node.prev node.ty in
  let binds = find_enclosing_lambdas prog node.prev [] in
  Printf.printf ("%i, %i, %i, %i: ") size (List.length vars) (List.length funcs) (List.length binds);
  let rules = [(List.length vars, create_var vars);
               (constructor_priority size prog node.ty, (create_constructor size));
               (size / 3, create_if);
               (size / 2, create_ext_function_call);
               (size / 2, let_insertion);
               (size * (List.length funcs) * 4, palka_rule funcs);
               (size * (List.length binds), not_useless_rule binds)] in
  (choose_frequency rules) prog e

let generate (st : state) (prog : Exp.program) : bool =
  match st.worklist.pop () with
  | None -> false
  | Some e ->
    let holes = generate_exp st.size prog e in
    List.iter (fun hole -> st.worklist.add hole) holes;
    Exp.check prog;
    st.size <- if st.size > 0 then st.size - 1 else 0;
    true

let generate_fp (size : int) (ty : Exp.ty) : Exp.program =
  let prog = Exp.make_program ty in
  let st = make_state size in
  st.worklist.add prog.head;
  let rec lp () =
    match generate st prog with
    | false -> prog
    | true -> lp() in
  lp()
