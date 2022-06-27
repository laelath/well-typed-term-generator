
(* Each node has a unique label, which cannot be changed. 
   if we have some node (call e1_l1 e2_l2) and we are updating e1 to (let (x rhs) e1), 
   it's tempting to overwrite the l1 label to point to this new node. 
   The problem is that we have update maps `type extension var -> program location set` 
   that point to where syntactic updates need to happen, and we don't want to update these.

   Each node also has a `prev` pointer, so there's no term sharing
   allowed; each node has exactly one reference.
 *)

let choose (lst : 'a list) : 'a = List.hd lst

type worklist = {
    pop : unit -> Exp.exp_label option;
    add : Exp.exp_label -> unit;
  }
type state = {
    program : Exp.program;
    worklist : worklist;
  }

exception InternalError of string

let assert_is_hole (Exp.ExpNode node) =
  match node.exp with
  | Exp.Hole -> ()
  | _ -> raise (InternalError "expression is not hole")



(* Implements the rule:
   E ~> E{alpha + tau} 
 *)
let extend_extvar st (extvar : Exp.extvar) (ext_ty : Exp.ty_label) = 
  let extend : 'a 'b . Exp.extvar -> (Exp.extvar -> 'a list) -> ('a -> unit) -> unit = 
    fun ext get add ->
    let lst = get ext in let handle_elt elt = add elt in
    List.iter handle_elt lst in

  let () = extend extvar st.program.extvar_ty_params 
                  (fun ty_params -> st.program.add_ty_param ty_params ext_ty) in
  let () = extend extvar st.program.extvar_params
                  (fun param -> st.program.add_param param (st.program.new_var())) in
  let () = extend extvar st.program.extvar_args 
                  (fun arg -> let node = Exp.ExpNode {exp = Exp.Hole; 
                                                   ty = ext_ty; 
                                                   prev = Some (st.program.args_prev arg)} in
                              st.program.add_arg arg (st.program.new_exp node)) in
  ()

(* takes E[e] and finds all lambdas i such that E_1[lambda_i xs . E_2[e]] *)
let rec find_enclosing_lambdas st (e : Exp.exp_label) acc : (Exp.params_label list) = 
  let Exp.ExpNode node = st.program.get_exp e in
  let acc = match node.exp with
    | Lambda lam -> lam.params :: acc
    | _ -> acc in
  match node.prev with
  | None -> acc
  | Some e -> find_enclosing_lambdas st e acc

(* Implements the rule:
   E_1[lambda_i xs alpha . E_2[<>]] ~> 
   E_1{alpha + tau}[lambda_i (x::xs) alpha . E_2{alpha + tau}[x]]

   via the decomposition

   E_1[lambda_i xs alpha . E_2[<>]] ~> 
   E_1{alpha + tau}[lambda_i (x::xs) alpha . E_2{alpha+tau}[<>]] ~> 
   E_1{alpha + tau}[lambda_i (x::xs) alpha . E_2{alpha + tau}[x]]

 *)
let not_useless_rule st (e : Exp.exp_label) =
  let Exp.ExpNode {ty=ty; prev=prev; _} = st.program.get_exp e in
  (* TODO: filter this by ty, don't want to cause circularities? *)
  let params = find_enclosing_lambdas st e [] in
  let param = choose params in
  let extvar = st.program.params_extvar param in
  let () = extend_extvar st extvar ty in

  let x = List.hd (st.program.get_params param) in
  let () = st.program.set_exp e (Exp.ExpNode {exp=Var {var=x}; ty=ty; prev=prev}) in
  ()

(* Implements the rule:
   E[<>] ~> E[call <> alpha] where alpha is fresh
 *)
let create_ext_function_call st (e : Exp.exp_label) =
  let Exp.ExpNode {ty=ty; prev=prev; _} = st.program.get_exp e in
  let extvar = st.program.new_extvar() in
  let f_ty_node = Exp.TyNode {ty = TyArrowExt (st.program.new_ty_params extvar, ty)} in
  let f_ty = st.program.new_ty f_ty_node in
  let f = st.program.new_exp (Exp.ExpNode {exp=Hole; ty=f_ty; prev=Some e}) in
  let args = st.program.new_args extvar in
  let () = st.program.set_exp e (Exp.ExpNode {exp = Call {func=f; args=args}; ty=ty; prev=prev}) in
  let () = st.worklist.add f in
  ()

let generate_exp (st : state) (e : Exp.exp_label) : state =
  let node = st.program.get_exp e in
  let () = assert_is_hole node in
  st

let generate (st : state) : state option =
  match st.worklist.pop () with
  | None -> None
  | Some e -> Some (generate_exp st e)


let generate_fp (st : state) : state =
  match generate st with
  | None -> st
  | Some st' -> st'







