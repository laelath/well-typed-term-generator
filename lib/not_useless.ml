
(* Each node has a unique label, which cannot be changed. 
   if we have some node (call e1_l1 e2_l2) and we are updating e1 to (let (x rhs) e1), 
   it's tempting to overwrite the l1 label to point to this new node. 
   The problem is that we have update maps `type extension var -> program location set` 
   that point to where syntactic updates need to happen, and we don't want to update these.

   Each node also has a `prev` pointer, so there's no term sharing
   allowed; each node has exactly one reference.
 *)

let choose (lst : 'a list) : 'a = List.hd lst
let choose_split (lst : 'a list) : 'a * ('a list) = List.hd lst, List.tl lst

type worklist = {
    pop : unit -> Exp.exp_label option;
    add : Exp.exp_label -> unit;
  }
type state = {
    worklist : worklist;
    mutable size : int;
  }

exception InternalError of string

let assert_is_hole (Exp.ExpNode node) =
  match node.exp with
  | Exp.Hole -> ()
  | _ -> raise (InternalError "expression is not hole")



(* Implements the rule:
   E ~> E{alpha + tau} 
 *)
let extend_extvar (prog : Exp.program) (extvar : Exp.extvar) (ext_ty : Exp.ty_label) = 
  let extend : 'a 'b . Exp.extvar -> (Exp.extvar -> 'a list) -> ('a -> unit) -> unit = 
    fun ext get add ->
    let lst = get ext in let handle_elt elt = add elt in
    List.iter handle_elt lst in

  let () = extend extvar prog.extvar_ty_params 
                  (fun ty_params -> prog.add_ty_param ty_params ext_ty) in
  let () = extend extvar prog.extvar_params
                  (fun param -> prog.add_param param (prog.new_var())) in
  let () = extend extvar prog.extvar_args 
                  (fun arg -> let node = Exp.ExpNode {exp = Exp.Hole; 
                                                      ty = ext_ty; 
                                                      prev = Some (prog.args_parent arg)} in
                              prog.add_arg arg (prog.new_exp node)) in
  ()

(* takes E[e] and finds all lambdas i such that E_1[lambda_i xs . E_2[e]] *)
let rec find_enclosing_lambdas (prog : Exp.program) (e : Exp.exp_label) acc : (Exp.params_label list) = 
  let Exp.ExpNode node = prog.get_exp e in
  let acc = match node.exp with
    | Lambda lam -> lam.params :: acc
    | _ -> acc in
  match node.prev with
  | None -> acc
  | Some e -> find_enclosing_lambdas prog e acc


(*
  TRANSITIONS 
 *)

exception BadTransition

(* Implements the rule:
   E_1[lambda_i xs alpha . E_2[<>]] ~> 
   E_1{alpha + tau}[lambda_i (x::xs) alpha . E_2{alpha + tau}[x]]

   via the decomposition

   E_1[lambda_i xs alpha . E_2[<>]] ~> 
   E_1{alpha + tau}[lambda_i (x::xs) alpha . E_2{alpha+tau}[<>]] ~> 
   E_1{alpha + tau}[lambda_i (x::xs) alpha . E_2{alpha + tau}[x]]

 *)
let not_useless_rule (_ : state) (prog : Exp.program) (e : Exp.exp_label) =
  let Exp.ExpNode {ty=ty; prev=prev; _} = prog.get_exp e in
  (* TODO: filter this by ty, don't want to cause circularities? *)
  let params = find_enclosing_lambdas prog e [] in
  let param = choose params in
  let extvar = prog.params_extvar param in
  let () = extend_extvar prog extvar ty in

  let x = List.hd (prog.get_params param) in
  let () = prog.set_exp e (Exp.ExpNode {exp=Var {var=x}; ty=ty; prev=prev}) in
  ()

(* Implements the rule:
   E[<>] ~> E[call <> alpha] where alpha is fresh
 *)
let create_ext_function_call (st : state) (prog : Exp.program) (e : Exp.exp_label) =
  let Exp.ExpNode {ty=ty; prev=prev; _} = prog.get_exp e in
  let extvar = prog.new_extvar() in
  let f_ty = prog.new_ty (Exp.TyNode {ty = Exp.TyArrowExt {ty_params=prog.new_ty_params extvar; ty_im=ty}}) in
  let f = prog.new_exp (Exp.ExpNode {exp=Hole; ty=f_ty; prev=Some e}) in
  let args = prog.new_args extvar e in
  let () = prog.set_exp e (Exp.ExpNode {exp = Call {func=f; args=args}; ty=ty; prev=prev}) in
  let () = st.worklist.add f in
  ()

(* Implements the rule:
   E[<>] ~> E[lambda xs alpha . <>]
 *)
let create_ext_lambda (st : state) (prog : Exp.program) (e : Exp.exp_label) = 
  let Exp.ExpNode {ty=ty; prev=prev; _} = prog.get_exp e in
  match prog.get_ty ty with
  | Exp.TyNode {ty = Exp.TyArrowExt {ty_params=ty_params; ty_im=ty_im}} -> 
     let extvar = prog.ty_params_extvar ty_params in
     let params_label = prog.new_params extvar in
     let xs = List.map (fun _ -> prog.new_var()) (prog.get_ty_params ty_params) in
     let () = List.iter (prog.add_param params_label) xs in
     let body = prog.new_exp (Exp.ExpNode {exp=Exp.Hole; ty=ty_im; prev=Some e}) in
     let () = prog.set_exp e (Exp.ExpNode {exp=Exp.Lambda {params=params_label; body=body}; ty=ty; prev=prev}) in
     let () = st.worklist.add body in
     ()
  | _ -> raise BadTransition

(* TODO: need to do environment management before this, or something *)
(* Implements the rule:
   E[<>] ~> E[x]
 *)

(* Implements the rule:
   E[<>] ~> E[dcon <> ... <>]
 *)

(* Implements the rule *)



(* 
   MAIN LOOP
 *) 

let generate_exp (st : state) (prog : Exp.program) (e : Exp.exp_label) =
  let node = prog.get_exp e in
  let () = assert_is_hole node in
  let transitions = [not_useless_rule; create_ext_function_call; create_ext_lambda] in
  let rec lp ts =
    let t, ts = choose_split ts in
    try t st prog e with
    | BadTransition -> lp ts in
  let () = lp transitions in
  ()

let generate (st : state) (prog : Exp.program) : bool =
  match st.worklist.pop () with
  | None -> false
  | Some e -> (generate_exp st prog e; true)


let generate_fp (st : state) (prog : Exp.program) : unit =
  let rec lp () = 
    match generate st prog with
    | false -> ()
    | true -> lp() in
  lp()







