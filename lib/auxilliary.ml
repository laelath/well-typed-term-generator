
(* Auxilliary program transformations used for testing. *)
   

(* finds a label of the program uniformly at random *)
let urn_of_subterms (prog : Exp.program) =
  let urn = ref (Urn.empty : Exp.ExpLabel.t Urn.t) in
  let add (l : Exp.ExpLabel.t) = urn := Urn.insert (!urn) 1.0 (Urn.Value l) in
  let rec find e =
    add e;
    let node = prog.get_exp e in
    match node.exp with
    | Hole -> ()
    | Var _ -> ()
    | StdLibRef _ -> ()
    | ValInt _ -> ()
    | Empty -> ()
    | Cons (e1, e2) -> 
       find e1; find e2
    | Match (e1, e2, (_, _, e3)) ->
       find e1; find e2; find e3
    | ValBool _ -> ()
    | Let (_, rhs, body) ->
       find rhs; find body
    | Lambda (_, body) ->
       find body
    | Call (func, args) ->
       find func; List.iter find args
    | ExtLambda (_, body) ->
       find body
    | ExtCall (func, args) ->
       find func; List.iter find (prog.get_args args)
    | If (pred, thn, els) ->
       find pred; find thn; find els
    | Custom _ -> () in
  find prog.head;
  !urn

let no_vars (prog : Exp.program) (e0 : Exp.ExpLabel.t) = 
  let rec find e =
    let node = prog.get_exp e in
    match node.exp with
    | Hole -> true
    | Var _ -> false
    | StdLibRef _ -> true
    | ValInt _ -> true
    | Empty -> true
    | Cons (e1, e2) -> 
       find e1 && find e2
    | Match (e1, e2, (_, _, e3)) ->
       find e1 && find e2 && find e3
    | ValBool _ -> true
    | Let (_, rhs, body) ->
       find rhs && find body
    | Lambda (_, body) ->
       find body
    | Call (func, args) ->
       find func && List.for_all find args
    | ExtLambda (_, body) ->
       find body
    | ExtCall (func, args) ->
       find func && List.for_all find (prog.get_args args)
    | If (pred, thn, els) ->
       find pred && find thn && find els
    | Custom _ -> true in
  find e0

let sample n = Random.float n

(* replaces two subterms (chosen uniformly) with errors using "Custom" *)
let remove_two (prog : Exp.program) =
  let set_prev e e' = 
    let node = prog.get_exp e in
    prog.set_exp e {exp=node.exp; ty=node.ty; prev=Some e'} in
  let subterms = urn_of_subterms prog in
  let e1 = Urn.sample sample subterms in
  let e2 = let rec find_diff () = 
             let e2 = Urn.sample sample subterms in
             if Exp.ExpLabel.equal e1 e2
             then find_diff()
             else e2 in
           find_diff() in
  (* TODO: technically we want two subterms that aren't beneath one another, but this should work for now *)
  (* TODO: abstract e1 e2 by variables in an outer lambda and apply it to the two error terms. *)
  let node1 = prog.get_exp e1 in
  let node2 = prog.get_exp e2 in
  let x = prog.new_var () in
  let y = prog.new_var () in
  let errorA = prog.new_exp {exp=Custom "(error \"A\")"; ty=node1.ty; prev=None} in
  let errorB = prog.new_exp {exp=Custom "(error \"B\")"; ty=node2.ty; prev=None} in
  let head = prog.head in
  let lambda = prog.new_exp {exp=Lambda ([x; y], head); ty=prog.ty.new_ty (TyArrow ([node1.ty; node2.ty], (prog.get_exp head).ty)); prev=None} in
  let head' = prog.new_exp {exp=Call (lambda, [errorA; errorB]); ty=(prog.get_exp head).ty; prev=None} in
  prog.set_exp e1 {exp=Var x; ty=node1.ty; prev=node1.prev};
  prog.set_exp e2 {exp=Var y; ty=node1.ty; prev=node1.prev};
  prog.head <- head';
  set_prev head lambda;
  set_prev lambda head';
  set_prev errorA head';
  set_prev errorB head';
  ()

(* replaces a subterm "e" (chosen uniformly) with a reference to a new variable "x", 
   and let-binds "e" to "x" at the top level of the program 
   E[e]  ~~~> let x=e in E[x]
   This will break in the presence of type variables since the type of "x" may refer to type variables.
 *)

let let_bind (prog : Exp.program) (to_string : Exp.program -> string) =
  (* set prev of e to be e' *)
  let set_prev e e' = 
    let node = prog.get_exp e in
    prog.set_exp e {exp=node.exp; ty=node.ty; prev=Some e'} in
  let subterms = urn_of_subterms prog in
  let e = let rec find_diff n = 
            if n = 0
            then None
            else
             let e = Urn.sample sample subterms in
             if Exp.ExpLabel.equal prog.head e || not (no_vars prog e)
             then find_diff (n-1)
             else Some e in
          find_diff 1000 in
  match e with
  | None -> (to_string prog, to_string prog)
  | Some e ->
     let node = prog.get_exp e in
     prog.set_exp e {exp=Custom "(error \"A\")"; ty=node.ty; prev=None};
     let string1 = to_string prog in
     let node = prog.get_exp e in
     let head = prog.head in
     let x = prog.new_var() in
     let e' = prog.new_exp {exp=node.exp (*Custom "(error \"A\")"*); ty=node.ty; prev=None} in
     let head_ty = (prog.get_exp head).ty in
     let head' = prog.new_exp {exp=Let (x, e', head); ty=head_ty; prev=None} in
     prog.head <- head';
     prog.set_exp e {exp=Var x; ty=node.ty; prev=node.prev};
     set_prev e' head';
     set_prev head head';
     let string2 = to_string prog in
     (string1, string2)


let diff_errors (prog : Exp.program) (error1 : string) (error2 : string) (to_string : Exp.program -> string) = 
  let subterms = urn_of_subterms prog in
  let e = Urn.sample sample subterms in
  let node = prog.get_exp e in
  prog.set_exp e {exp = Custom error1; ty=node.ty; prev=node.prev};
  let string1 = to_string prog in
  prog.set_exp e {exp = Custom error2; ty=node.ty; prev=node.prev};
  let string2 = to_string prog in
  (string1, string2)
