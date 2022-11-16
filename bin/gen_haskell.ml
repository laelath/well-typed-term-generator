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

    let ty = prog.get_ty tyl in
    match ty with
    | TyNdInt -> "Int"
    | TyNdBool -> "Bool"
    | TyNdList tyl' -> "[" ^ str_ty tyl' ^ "]"
    | TyNdArrow (params, tyl') -> "(" ^ str_ty_params params ^ str_ty tyl' ^ ")"
    | TyNdArrowExt (params, tyl') -> "(" ^ str_ty_params (prog.get_ty_params params) ^ str_ty tyl' ^ ")"
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
  Generate.generate_fp Generators.main ~std_lib:haskell_std_lib size (Exp.TyArrow ([Exp.TyList Exp.TyInt], (Exp.TyList Exp.TyInt)))

let generate_palka_batch batch size =
  let rec gen_batch batch acc =
    if batch == 0
    then acc
    else let p = generate_palka size in
         Printf.eprintf "\n";
         gen_batch (batch - 1) (haskell_string p :: acc)
  in
  gen_batch batch []

let generate_palka_file ?(sep = "====") batch size =
  let fs = generate_palka_batch batch size in
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
