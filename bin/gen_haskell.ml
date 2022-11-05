exception FoundHole
exception IllTyped

let haskell_string (prog : Exp.program) =

  let rec str_ty tyl =
    let str_ty_params params =
      match params with
      | [] -> "() -> "
      | _ ->
        List.fold_left
          (fun acc tyl -> str_ty tyl ^ " -> " ^ acc)
          "" params
    in

    let ty = prog.get_ty tyl in
    match ty with
    | TyNdInt -> "Int"
    | TyNdBool -> "Bool"
    | TyNdList tyl' -> "[" ^ str_ty tyl' ^ "]"
    | TyNdArrow (params, tyl') -> "(" ^ str_ty_params params ^ str_ty tyl' ^ ")"
    | TyNdArrowExt (params, tyl') -> "(" ^ str_ty_params (prog.get_ty_params params) ^ str_ty tyl' ^ ")"
  in

  let str_var var ty = "(" ^ Exp.Var.to_string var ^ "::" ^ str_ty ty ^ ")" in

  let str_params params ty_params =
    match params with
    | [] -> "\\_ -> "
    | _ -> List.fold_left2
             (fun acc var ty -> "\\" ^ str_var var ty ^ " -> " ^ acc)
             "" params ty_params
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

    let needs_annotation str =
      match str with
      | "undefined" -> true
      | _ -> false
    in

    let node = prog.get_exp e in
    match node.exp with
    | Hole -> raise FoundHole
    | Var var -> Exp.Var.to_string var
    | StdLibRef str ->
      if needs_annotation str
      then "(" ^ str ^ "::" ^ str_ty node.ty ^ ")"
      else str
    | ValInt i -> Int.to_string i
    | ValBool b -> (match b with
                    | true -> "True"
                    | false -> "False")
    | Empty -> "([]::" ^ str_ty node.ty ^ ")"
    | Cons (fst, rst) -> "(" ^ (str_exp fst) ^ " : " ^ (str_exp rst) ^ ")"
    | Match (value, nil_case, (x_fst, x_rst, cons_case)) ->
      "(case (" ^ (str_exp value) ^ "::" ^ str_ty (prog.get_exp value).ty ^ ") of {"
      ^ "[] -> " ^ (str_exp nil_case) ^ "; "
      ^ Exp.Var.to_string x_fst ^ ":" ^ Exp.Var.to_string x_rst ^ " -> " ^ (str_exp cons_case) ^ "})"
    | Let (var, rhs, body) ->
      "(let " ^ str_var var (prog.get_exp rhs).ty
      ^ " = " ^ str_exp rhs
      ^ " in " ^ str_exp body ^ ")"
    | Lambda (params, body) ->
      (match (prog.get_ty node.ty) with
       | TyNdArrow (ty_params, _) ->
         "(" ^ str_params params ty_params ^ str_exp body ^ ")"
       | _ -> raise IllTyped)
    | Call (func, args) ->
      "(" ^ str_exp func ^ str_args args ^ ")"
    | ExtLambda (params, body) ->
      (match (prog.get_ty node.ty) with
       | TyNdArrowExt (ty_params, _) ->
         "(" ^ str_params (prog.get_params params) (prog.get_ty_params ty_params) ^ str_exp body ^ ")"
       | _ -> raise IllTyped)
    | ExtCall (func, args) ->
      "(" ^ str_exp func ^ str_args (prog.get_args args) ^ ")"
    | If (pred, thn, els) ->
      "(if " ^ str_exp pred
      ^ " then " ^ str_exp thn
      ^ " else " ^ str_exp els ^ ")"
  in
  str_exp prog.head

let haskell_std_lib =
  let open Exp in
  [("seq", (TyArrow ([TyVar "b"; TyVar "a"], TyVar "a"), 1));
   ("id", (TyArrow ([TyVar "a"], TyVar "a"), 2));
   ("(+)", (TyArrow ([TyInt; TyInt], TyInt), 1));
   ("(+1)", (TyArrow ([TyInt], TyInt), 1));
   ("(-)", (TyArrow ([TyInt; TyInt], TyInt), 1));
   ("head", (TyArrow ([TyList (TyVar "a")], TyVar "a"), 3));
   ("tail", (TyArrow ([TyList (TyVar "a")], TyList (TyVar "a")), 3));
   ("take", (TyArrow ([TyInt; TyList (TyVar "a")], TyList (TyVar "a")), 4));
   ("(!!)", (TyArrow ([TyList (TyVar "a"); TyInt], TyVar "a"), 4));
   ("length", (TyArrow ([TyList (TyVar "a")], TyInt), 1));
   ("(++)", (TyArrow ([TyList (TyVar "a"); TyList (TyVar "a")],
                      TyList (TyVar "a")), 1));
   ("filter", (TyArrow ([TyArrow ([TyVar "a"], TyBool); TyList (TyVar "a")],
                        TyList (TyVar "a")), 1));
   ("map", (TyArrow ([TyArrow ([TyVar "a"], TyVar "b"); TyList (TyVar "a")],
                     TyList (TyVar "b")), 1));
   ("foldr", (TyArrow ([TyArrow ([TyVar "b"; TyVar "a"],
                                 TyVar "a");
                        TyVar "a"; TyList (TyVar "b")],
                       TyVar "a"), 1));
   ("odd", (TyArrow ([TyInt], TyBool), 1));
   ("even", (TyArrow ([TyInt], TyBool), 1));
   ("(&&)", (TyArrow ([TyBool; TyBool], TyBool), 1));
   ("(||)", (TyArrow ([TyBool; TyBool], TyBool), 1));
   ("not", (TyArrow ([TyBool], TyBool), 1));
   ("((==)::Int -> Int -> Bool)", (TyArrow ([TyInt; TyInt], TyBool), 1));
   ("((==)::Bool -> Bool -> Bool)", (TyArrow ([TyBool; TyBool], TyBool), 1));
   ("((==)::[Int] -> [Int] -> Bool)", (TyArrow ([TyList TyInt; TyList TyInt], TyBool), 1));
   ("undefined", (TyVar "a", 32));
  ]

let generate_palka size =
  NotUseless.generate_fp ~std_lib:haskell_std_lib size (Exp.TyArrow ([Exp.TyList Exp.TyInt], (Exp.TyList Exp.TyInt)))

let generate_palka_batch batch size =
  let rec gen_batch batch acc =
    if batch == 0
    then acc
    else let p = generate_palka size in
         Printf.eprintf "\n";
         gen_batch (batch - 1) (haskell_string p :: acc)
  in
  gen_batch batch []

let generate_palka_file batch size =
  let fs = generate_palka_batch batch size in
  "things :: [[Int] -> [Int]]\nthings = [\n  " ^ String.concat ",\n  " fs ^ "\n  ]\n"


let n = ref 100
let size = ref 100
let seed = ref (-1)

let speclist =
  [
    ("-n", Arg.Set_int n, "Number of functions to generate");
    ("-size", Arg.Set_int size, "Size of each function");
    ("-seed", Arg.Set_int seed, "Random generator seed");
  ]

let () =
  Arg.parse speclist (fun _ -> ()) "gen_haskell [-n <100>] [-size <100>] [-seed <-1>";
  (if !seed < 0
   then Random.self_init ()
   else Random.init !seed);
  print_string (generate_palka_file !n !size)
