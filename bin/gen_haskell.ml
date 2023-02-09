exception FoundHole

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

    let ty = prog.ty.get_ty tyl in
    match ty with
    | TyInt -> "Int"
    | TyBool -> "Bool"
    | TyList tyl' -> "[" ^ str_ty tyl' ^ "]"
    | TyArrow (params, tyl') -> "(" ^ str_ty_params params ^ str_ty tyl' ^ ")"
    | TyArrowExt (params, tyl') -> "(" ^ str_ty_params (prog.ty.get_ty_params params) ^ str_ty tyl' ^ ")"
  in

  (* let str_var var ty = "(" ^ Exp.Var.to_string var ^ "::" ^ str_ty ty ^ ")" in *)
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

    let needs_annotation str =
      match str with
      | "[]" | "undefined" | "length" | "foldr" -> true
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
    | Cons (fst, rst) -> "(" ^ str_exp fst ^ " : " ^ str_exp rst ^ ")"
    | Match (value, nil_case, (x_fst, x_rst, cons_case)) ->
      "(case " ^ str_exp value ^ " of {"
      ^ "[] -> " ^ str_exp nil_case ^ "; "
      ^ str_var x_fst ^ ":" ^ str_var x_rst ^ " -> " ^ str_exp cons_case ^ "})"
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
  str_exp prog.head

(* NOTE: no enumFromTo(') or case1 *)
let haskell_std_lib =
  let open Type in
  [("seq", (FlatTyArrow ([FlatTyVar "b"; FlatTyVar "a"], FlatTyVar "a"), 1));
   ("id", (FlatTyArrow ([FlatTyVar "a"], FlatTyVar "a"), 2));
   ("0", (FlatTyInt, 1));
   ("1", (FlatTyInt, 1));
   ("2", (FlatTyInt, 1));
   ("(+)", (FlatTyArrow ([FlatTyInt; FlatTyInt], FlatTyInt), 1));
   ("(+1)", (FlatTyArrow ([FlatTyInt], FlatTyInt), 1));
   ("(-)", (FlatTyArrow ([FlatTyInt; FlatTyInt], FlatTyInt), 1));
   ("[]", (FlatTyList (FlatTyVar "a"), 1));
   ("(:)", (FlatTyArrow ([FlatTyVar "a"; FlatTyList (FlatTyVar "a")], FlatTyList (FlatTyVar "a")), 1));
   ("head", (FlatTyArrow ([FlatTyList (FlatTyVar "a")], FlatTyVar "a"), 3));
   ("tail", (FlatTyArrow ([FlatTyList (FlatTyVar "a")], FlatTyList (FlatTyVar "a")), 3));
   ("take", (FlatTyArrow ([FlatTyInt; FlatTyList (FlatTyVar "a")], FlatTyList (FlatTyVar "a")), 4));
   ("(!!)", (FlatTyArrow ([FlatTyList (FlatTyVar "a"); FlatTyInt], FlatTyVar "a"), 4));
   ("length", (FlatTyArrow ([FlatTyList (FlatTyVar "a")], FlatTyInt), 1));
   ("(++)", (FlatTyArrow ([FlatTyList (FlatTyVar "a"); FlatTyList (FlatTyVar "a")],
                      FlatTyList (FlatTyVar "a")), 1));
   ("filter", (FlatTyArrow ([FlatTyArrow ([FlatTyVar "a"], FlatTyBool); FlatTyList (FlatTyVar "a")],
                        FlatTyList (FlatTyVar "a")), 1));
   ("map", (FlatTyArrow ([FlatTyArrow ([FlatTyVar "a"], FlatTyVar "b"); FlatTyList (FlatTyVar "a")],
                     FlatTyList (FlatTyVar "b")), 1));
   ("foldr", (FlatTyArrow ([FlatTyArrow ([FlatTyVar "b"; FlatTyVar "a"],
                                 FlatTyVar "a");
                        FlatTyVar "a"; FlatTyList (FlatTyVar "b")],
                       FlatTyVar "a"), 1));
   ("odd", (FlatTyArrow ([FlatTyInt], FlatTyBool), 1));
   ("even", (FlatTyArrow ([FlatTyInt], FlatTyBool), 1));
   ("(&&)", (FlatTyArrow ([FlatTyBool; FlatTyBool], FlatTyBool), 1));
   ("(||)", (FlatTyArrow ([FlatTyBool; FlatTyBool], FlatTyBool), 1));
   ("not", (FlatTyArrow ([FlatTyBool], FlatTyBool), 1));
   ("True", (FlatTyBool, 1));
   ("False", (FlatTyBool, 1));
   ("((==)::Int -> Int -> Bool)", (FlatTyArrow ([FlatTyInt; FlatTyInt], FlatTyBool), 1));
   ("((==)::Bool -> Bool -> Bool)", (FlatTyArrow ([FlatTyBool; FlatTyBool], FlatTyBool), 1));
   ("((==)::[Int] -> [Int] -> Bool)", (FlatTyArrow ([FlatTyList FlatTyInt; FlatTyList FlatTyInt], FlatTyBool), 1));
   ("undefined", (FlatTyVar "a", 32));
  ]

let generate_palka size =
  let open Type in
  Generate.generate_fp Generators.palka ~std_lib:haskell_std_lib size (FlatTyArrow ([FlatTyList FlatTyInt], (FlatTyList FlatTyInt)))

let generate_not_useless size =
  let open Type in
  Generate.generate_fp Generators.main ~std_lib:haskell_std_lib size (FlatTyArrow ([FlatTyList FlatTyInt], (FlatTyList FlatTyInt)))

let generate_batch (generate : int -> Exp.program) batch size =
  let rec gen_batch batch acc =
    if batch == 0
    then acc
    else let p = generate size in
         Printf.eprintf "\n";
         gen_batch (batch - 1) (haskell_string p :: acc)
  in
  gen_batch batch []

let generate_file ?(sep = "====") (generate : int -> Exp.program) batch size =
  let fs = generate_batch generate batch size in
  "module Main where\n" ^
  "import Control.Monad\n" ^
  "import qualified Control.Exception as E\n" ^
  "import System.IO (hSetBuffering, stdout, BufferMode (NoBuffering))\n" ^
  "handler (E.ErrorCall s) = putStrLn $ \"*** Exception: \"\n" ^
  "incomplete1 0 = [undefined]\n" ^
  "incomplete1 n = n:(incomplete1 (n-1))\n" ^
  "incomplete2 0 = undefined\n" ^
  "incomplete2 n = n:(incomplete2 (n-1))\n" ^
  "incomplete3 n 0 = undefined:reverse [0..n-1]\n" ^
  "incomplete3 n m = n:incomplete3 (n-1) (m-1)\n" ^
  "codeList :: [[Int] -> [Int]]\n" ^
  "codeList = [\n  " ^ String.concat ",\n  " fs ^ "\n  ]\n" ^
  "main = do\n" ^
  "  hSetBuffering stdout NoBuffering\n" ^
  "  forM_ codeList $ \\code -> do\n" ^
  "    forM_ [0..5] $ \\x -> do\n" ^
  "      E.catch (print $ code $ incomplete1 x) handler\n" ^
  "    forM_ [0..5] $ \\x -> do\n" ^
  "      E.catch (print $ code $ incomplete2 x) handler\n" ^
  "    forM_ [0..5] $ \\x -> forM_ [0..x] $ \\y -> do\n" ^
  "      E.catch (print $ code $ incomplete3 x y) handler\n" ^
  "    putStrLn \"" ^ sep ^ "\"\n"


let n = ref 100
let size = ref 100
let seed = ref (-1)
let gen_type_palka = "palka"
let gen_type_not_useless = "not_useless"
let gen_type = ref gen_type_palka

let speclist =
  [
    ("-n", Arg.Set_int n, "Number of functions to generate");
    ("-size", Arg.Set_int size, "Size of each function");
    ("-seed", Arg.Set_int seed, "Random generator seed");
    ("-type", Arg.Set_string gen_type, "Generator type (\"" ^ gen_type_palka ^ "\" or \"" ^ gen_type_not_useless ^ "\")");
  ]

let () =
  Arg.parse speclist (fun _ -> ()) "gen_haskell [-n <100>] [-size <100>] [-seed <-1>";
  (if !seed < 0
   then Random.self_init ()
   else Random.init !seed);
  let gen_type = let s = !gen_type in
                 if s = gen_type_palka
                 then generate_palka
                 else if s = gen_type_not_useless
                 then generate_not_useless
                 else raise Util.Unimplemented in
  print_string (generate_file gen_type (!n) (!size))
