
exception FoundHole

let print (prog : Exp.program) =
  let str_var = Exp.Var.to_string in

  let str_params params =
    match params with
    | [] -> "\\_ -> "
    | _ -> List.fold_left
             (fun acc var -> "\\" ^ str_var var ^ " -> " ^ acc)
             "" params
  in

  let rec str_exp e =
  (* let str_type ty = raise *)

    let str_args args =
      match args with
      | [] -> " ()"
      | _ -> List.fold_left
               (fun acc arg -> " " ^ (str_exp arg) ^ acc)
               "" args
    in

    let node = prog.get_exp e in
    match node.exp with
    | Hole -> raise FoundHole
    | Var var -> str_var var
    | StdLibRef str -> str
    | ValInt i -> Int.to_string i
    | ValBool b -> (match b with
                    | true -> "True"
                    | false -> "False")
    | Empty -> "[]"
    | Cons (fst, rst) -> "(" ^ (str_exp fst) ^ " : " ^ (str_exp rst) ^ ")"
    | Match (value, nil_case, (x_fst, x_rst, cons_case)) ->
       "(case " ^ (str_exp value) ^ " of {"
       ^ "[] -> " ^ (str_exp nil_case) ^ "; "
       ^ (str_var x_fst) ^ ":" ^ (str_var x_rst) ^ " -> " ^ (str_exp cons_case) ^ "})"
    | Let (var, rhs, body) ->
       "(let " ^ str_var var
       ^ " = " ^ str_exp rhs
       ^ " in " ^ str_exp body ^ ")"
    | Lambda (params, body) ->
       "(" ^ str_params params ^ str_exp body ^ ")"
    | Call (func, args) ->
       "(" ^ str_exp func ^ str_args args ^ ")"
    | ExtLambda (params, body) ->
       "(" ^ str_params (prog.get_params params) ^ str_exp body ^ ")"
    | ExtCall (func, args) ->
       "(" ^ str_exp func ^ str_args (prog.get_args args) ^ ")"
    | If (pred, thn, els) ->
       "(if " ^ str_exp pred
       ^ " then " ^ str_exp thn
       ^ " else " ^ str_exp els ^ ")"
  in
  print_string (str_exp prog.head);
  print_string("\n")
