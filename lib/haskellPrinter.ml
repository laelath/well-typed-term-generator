
exception FoundHole

let print (prog : Exp.program) =
  let string_of_params params =
    match prog.get_params params with
    | [] -> "\\_ -> "
    | x :: xs ->
       String.concat "" (List.map (fun var -> "\\" ^ Exp.Var.to_string var ^ " -> ") (x :: xs))
  in

  let rec string_of_exp e =
  (* let string_of_type ty = raise *)

    let string_of_args args =
      match prog.get_args args with
      | [] -> " ()"
      | arg :: args ->
         String.concat " " (List.map (fun arg -> " " ^ (string_of_exp arg)) (arg :: args))
    in

    let node = prog.get_exp e in
    match node.exp with
    | Hole -> raise FoundHole
    | Var var -> Exp.Var.to_string var
    | ValInt i -> Int.to_string i
    | ValBool b -> (match b with
                    | true -> "True"
                    | false -> "False")
    | Empty -> "[]"
    | Cons (_ee, _el) -> "" (* TODO *)
    | Match (_e1, _e2, (_x, _y, _e3)) -> "" (* TODO *)
    | Let (var, rhs, body) ->
       "(let " ^ Exp.Var.to_string var
       ^ " = " ^ string_of_exp rhs
       ^ " in " ^ string_of_exp body ^ ")"
    | Lambda (_params, _body) -> "" (* TODO *)
    | Call (_func, _args) -> "" (* TODO *)
    | ExtLambda (params, body) ->
       "(" ^ string_of_params params ^ string_of_exp body ^ ")"
    | ExtCall (func, args) ->
       "(" ^ string_of_exp func ^ string_of_args args ^ ")"
    | If (pred, thn, els) ->
       "(if " ^ string_of_exp pred
       ^ " then " ^ string_of_exp thn
       ^ " else " ^ string_of_exp els ^ ")" in
  print_string (string_of_exp prog.head);
  print_string("\n")
