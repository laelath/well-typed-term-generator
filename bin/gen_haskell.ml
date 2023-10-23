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

    let str_args args =
      match args with
      | [] -> " ()"
      | _ -> List.fold_left
               (fun acc arg -> " " ^ (str_exp arg) ^ acc)
               "" args
    in

    let needs_annotation str =
      match str with
      | "[]" | "undefined" -> true
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
      "((" ^ str_params params ^ str_exp body ^ ")::" ^ str_ty node.ty ^ ")"
    | Call (func, args) ->
      "(" ^ str_exp func ^ str_args args ^ ")"
    | ExtLambda (params, body) ->
      "((" ^ str_params (prog.get_params params) ^ str_exp body ^ ")::" ^ str_ty node.ty ^ ")"
    | ExtCall (func, args) ->
      "(" ^ str_exp func ^ str_args (prog.get_args args) ^ ")"
    | If (pred, thn, els) ->
      "(if " ^ str_exp pred
      ^ " then " ^ str_exp thn
      ^ " else " ^ str_exp els ^ ")"
    | Custom str -> str
  in
  str_exp prog.head

(* NOTE: no enumFromTo(') or case1 *)
let haskell_std_lib =
  let open Type in
  [("seq", FlatTyArrow ([FlatTyVar "b"; FlatTyVar "a"], FlatTyVar "a"));
   ("id", FlatTyArrow ([FlatTyVar "a"], FlatTyVar "a"));
   ("0", FlatTyInt);
   ("1", FlatTyInt);
   ("2", FlatTyInt);
   ("(+)", FlatTyArrow ([FlatTyInt; FlatTyInt], FlatTyInt));
   ("(+1)", FlatTyArrow ([FlatTyInt], FlatTyInt));
   ("(-)", FlatTyArrow ([FlatTyInt; FlatTyInt], FlatTyInt));
   ("[]", FlatTyList (FlatTyVar "a"));
   ("(:)", FlatTyArrow ([FlatTyVar "a"; FlatTyList (FlatTyVar "a")], FlatTyList (FlatTyVar "a")));
   ("head", FlatTyArrow ([FlatTyList (FlatTyVar "a")], FlatTyVar "a"));
   ("tail", FlatTyArrow ([FlatTyList (FlatTyVar "a")], FlatTyList (FlatTyVar "a")));
   ("take", FlatTyArrow ([FlatTyInt; FlatTyList (FlatTyVar "a")], FlatTyList (FlatTyVar "a")));
   ("(!!)", FlatTyArrow ([FlatTyList (FlatTyVar "a"); FlatTyInt], FlatTyVar "a"));
   ("length", FlatTyArrow ([FlatTyList (FlatTyVar "a")], FlatTyInt));
   ("(++)", FlatTyArrow ([FlatTyList (FlatTyVar "a"); FlatTyList (FlatTyVar "a")],
                         FlatTyList (FlatTyVar "a")));
   ("filter", FlatTyArrow ([FlatTyArrow ([FlatTyVar "a"], FlatTyBool); FlatTyList (FlatTyVar "a")],
                           FlatTyList (FlatTyVar "a")));
   ("map", FlatTyArrow ([FlatTyArrow ([FlatTyVar "a"], FlatTyVar "b"); FlatTyList (FlatTyVar "a")],
                        FlatTyList (FlatTyVar "b")));
   ("foldr", FlatTyArrow ([FlatTyArrow ([FlatTyVar "b"; FlatTyVar "a"], FlatTyVar "a");
                           FlatTyVar "a"; FlatTyList (FlatTyVar "b")],
                          FlatTyVar "a"));
   ("odd", FlatTyArrow ([FlatTyInt], FlatTyBool));
   ("even", FlatTyArrow ([FlatTyInt], FlatTyBool));
   ("(&&)", FlatTyArrow ([FlatTyBool; FlatTyBool], FlatTyBool));
   ("(||)", FlatTyArrow ([FlatTyBool; FlatTyBool], FlatTyBool));
   ("not", FlatTyArrow ([FlatTyBool], FlatTyBool));
   ("True", FlatTyBool);
   ("False", FlatTyBool);
   ("((==)::Int -> Int -> Bool)", FlatTyArrow ([FlatTyInt; FlatTyInt], FlatTyBool));
   ("((==)::Bool -> Bool -> Bool)", FlatTyArrow ([FlatTyBool; FlatTyBool], FlatTyBool));
   ("((==)::[Int] -> [Int] -> Bool)", FlatTyArrow ([FlatTyList FlatTyInt; FlatTyList FlatTyInt], FlatTyBool));
   ("undefined", FlatTyVar "a");
  ]



let generate_palka _size =
  raise Util.Unimplemented
(*
  let open Type in
  Generate.generate_fp Generators.palka ~std_lib:haskell_std_lib size (FlatTyArrow ([FlatTyList FlatTyInt], (FlatTyList FlatTyInt)))
*)

let generate_not_useless std_lib size =
  let std_lib_m x = 
    match x with
    | "head" | "tail" -> 1. /. 2.
    | "(!!)" -> 1. /. 3.
    | "undefined" -> 1. /. 10.
    | _ -> 1. in
  let open Type in
  let gen_ty = FlatTyArrow ([FlatTyList FlatTyInt], FlatTyList FlatTyInt) in
  Generate.generate_fp (Generators.main std_lib_m) ~std_lib:std_lib size gen_ty

let generate_batch (generate : (string * Type.flat_ty) list -> int -> Exp.program) std_lib batch size =
  let rec gen_batch batch acc =
    if batch == 0
    then acc
    else let p = generate std_lib size in
         Debug.say (fun () -> "\n");
         gen_batch (batch - 1) (p :: acc)
  in
  let progs = gen_batch batch [] in
  Debug.run(fun () ->
              let (ts, us) = List.split (List.map (Exp.count_binds Exp.flag_count_lambda) progs) in
              Printf.eprintf "Lambdas: Total: %i, Unused: %i\n" (List.fold_left (+) 0 ts) (List.fold_left (+) 0 us);
              let (ts, us) = List.split (List.map (Exp.count_binds Exp.flag_count_ext_lambda) progs) in
              Printf.eprintf "Ext. Lambdas: Total: %i, Unused: %i\n" (List.fold_left (+) 0 ts) (List.fold_left (+) 0 us);
              let (ts, us) = List.split (List.map (Exp.count_binds Exp.flag_count_let) progs) in
              Printf.eprintf "Lets: Total: %i, Unused: %i\n" (List.fold_left (+) 0 ts) (List.fold_left (+) 0 us));
  progs

let generate_file ?(sep = "====") fs handler prelude tyann code =
  "module Main where\n" ^
  "import Control.Monad\n" ^
  "import qualified Control.Exception as E\n" ^
  "import System.IO (hSetBuffering, stdout, BufferMode (NoBuffering))\n" ^
  handler ^ "\n" ^
  "incomplete1 0 = [undefined]\n" ^
  "incomplete1 n = n:(incomplete1 (n-1))\n" ^
  "incomplete2 0 = undefined\n" ^
  "incomplete2 n = n:(incomplete2 (n-1))\n" ^
  "incomplete3 n 0 = undefined:reverse [0..n-1]\n" ^
  "incomplete3 n m = n:incomplete3 (n-1) (m-1)\n" ^
  prelude ^ "\n" ^
  "codeList :: " ^ tyann ^ "\n" ^
  "codeList = [\n  " ^ String.concat ",\n  " fs ^ "\n  ]\n" ^
  "main = do\n" ^
  "  hSetBuffering stdout NoBuffering\n" ^
  code sep

let one_code sep = 
  "  forM_ codeList $ \\code -> do\n" ^
  "    forM_ [0..5] $ \\x -> do\n" ^
  "      E.catch (print $ code $ incomplete1 x) handler\n" ^
  "    forM_ [0..5] $ \\x -> do\n" ^
  "      E.catch (print $ code $ incomplete2 x) handler\n" ^
  "    forM_ [0..5] $ \\x -> forM_ [0..x] $ \\y -> do\n" ^
  "      E.catch (print $ code $ incomplete3 x y) handler\n" ^
  "    putStrLn \"" ^ sep ^ "\"\n"

let two_code sep = 
  "  forM_ codeList $ \\(code1, code2) -> do\n" ^
  "    forM_ [0..5] $ \\x -> do\n" ^
  "      do (E.catch (print $ code1 $ incomplete1 x) handler); (E.catch (print $ code2 $ incomplete1 x) handler)\n" ^
  "    forM_ [0..5] $ \\x -> do\n" ^
  "      do (E.catch (print $ code1 $ incomplete2 x) handler); (E.catch (print $ code2 $ incomplete2 x) handler)\n" ^
  "    forM_ [0..5] $ \\x -> forM_ [0..x] $ \\y -> do\n" ^
  "      do (E.catch (print $ code1 $ incomplete3 x y) handler); (E.catch (print $ code2 $ incomplete3 x y) handler)\n" ^
  "    putStrLn \"" ^ sep ^ "\"\n"


(* -O -fno-full-laziness *)
let testtype0 gen_type n size = 
  let generate = gen_type in
  let batch = n in
  let fs = List.map haskell_string (generate_batch generate haskell_std_lib batch size) in
  print_string (generate_file fs "handler (E.ErrorCall s) = putStrLn $ \"*** Exception: \"" "" "[[Int] -> [Int]]" one_code)

(* -O -fno-full-laziness *)
let testtype1 gen_type n size = 
  let generate = gen_type in
  let batch = n in
  let fs = List.map (fun e -> Auxilliary.remove_two e; haskell_string e)
                    (generate_batch generate haskell_std_lib batch size) in
  print_string (generate_file fs "handler (E.ErrorCall s) = putStrLn $ \"*** Exception: \" ++ s" "" "[[Int] -> [Int]]" one_code)

let testtype2 gen_type n size = 
  let generate = gen_type in
  let batch = n in
  let std_lib = haskell_std_lib @ [("(error \"A\")", Type.FlatTyVar "a")] in
  let fs = List.map (fun e -> let (e1, e2) = Auxilliary.let_bind e haskell_string in
                              "(" ^ e1 ^ ", " ^ e2 ^ ")")
                    (generate_batch generate std_lib batch size) in
  print_string (generate_file fs "handler (E.ErrorCall s) = putStrLn $ \"*** Exception: \"" "" "[([Int] -> [Int], [Int] -> [Int])]" two_code)

let testtype3 gen_type n size = 
  let generate = gen_type in
  let batch = n in
  let fs = List.map (fun e -> let (e1, e2) = Auxilliary.diff_errors e "hiddenError" "undefined" haskell_string in
                              "(" ^ e1 ^ ", " ^ e2 ^ ")")
                    (generate_batch generate haskell_std_lib batch size) in
  print_string (generate_file fs "handler (E.ErrorCall s) = putStrLn $ \"*** Exception: \"" "hiddenError = error \"hidden error\"" "[([Int] -> [Int], [Int] -> [Int])]" two_code)


let n = ref 100
let size = ref 25
let seed = ref (-1)
let gen_type_palka = "palka"
let gen_type_not_useless = "not_useless"
let gen_type = ref gen_type_not_useless
let testtype = ref 0

let speclist =
  [
    ("-n", Arg.Set_int n, "Number of functions to generate");
    ("-size", Arg.Set_int size, "Size of each function");
    ("-seed", Arg.Set_int seed, "Random generator seed");
    ("-type", Arg.Set_string gen_type, "Generator type (\"" ^ gen_type_palka ^ "\" or \"" ^ gen_type_not_useless ^ "\")");
    ("-testtype", Arg.Set_int testtype, "Test type (\"" ^ "0 or 1 or 2 or 3" ^ "\")");
  ]

let () =
  Arg.parse speclist (fun _ -> ()) "gen_haskell [-testtype <0>] [-n <100>] [-size <100>] [-seed <-1>";
  (if !seed < 0
   then Random.self_init ()
   else Random.init !seed);
  let gen_type = let s = !gen_type in
                 if s = gen_type_palka
                 then generate_palka
                 else if s = gen_type_not_useless
                 then generate_not_useless
                 else raise Util.Unimplemented in
  match !testtype with
  | 0 -> testtype0 gen_type (!n) (!size)
  | 1 -> testtype1 gen_type (!n) (!size)
  | 2 -> testtype2 gen_type (!n) (!size)
  | 3 -> testtype3 gen_type (!n) (!size)
  | _ -> raise Util.Unimplemented
