open External

(* TODO: type annotations *)
let _ty_string (_ty : ty) : string = raise Util.Unimplemented

let is_infix f =
  match f with
  | "(+)" | "(-)"
    | "(:)" | "(!!)" | "(++)"
    | "(&&)" | "(||)" -> true
  | _ -> false

let make_infix f =
  String.sub f 1 (String.length f - 2)

let rec haskell_string e =
  match e with
  | Ref (x, _ty) -> x
  | Lambda (xs, e_body) ->
     (match xs with
      | [] -> haskell_string e_body
      | _ ->
         "(\\" ^ String.concat " " (List.map fst xs) ^
         " -> " ^ haskell_string e_body ^ ")")
  | Call (e_f, e_args) ->
    (match e_f, e_args with
     | Ref (f, _), [e1; e2] when is_infix f ->
        "(" ^ haskell_string e1 ^
        " " ^ make_infix f ^ " " ^
        haskell_string e2 ^ ")"
     | _, _ ->
        match e_args with
        | [] -> haskell_string e_f
        | _ ->
          "(" ^ haskell_string e_f ^ " " ^
          String.concat " " (List.map haskell_string e_args) ^ ")")
  | Let ((_, _), _, _) -> raise Util.Unimplemented


let (-->) ty_params ty_body = TyFun (ty_params, ty_body)
let tInt = TyCons ("Int", [])
let tBool = TyCons ("Bool", [])
let tList ty = TyCons ("([])", [ty])
let tVar a = TyVar a

(* NOTE: no enumFromTo(') or case1 *)
let haskell_std_lib =
  [("seq",    [tVar "b"; tVar "a"] --> (tVar "a"));
   ("id",     [tVar "a"] --> tVar "a");
   ("0",      tInt);
   ("1",      tInt);
   ("2",      tInt);
   ("(+)",    [tInt; tInt] --> tInt);
   ("(+1)",   [tInt] --> tInt);
   ("(-)",    [tInt; tInt] --> tInt);
   ("[]",     tList (tVar "a"));
   ("(:)",    [tVar "a"; tList (tVar "a")] --> tList (tVar "a"));
   ("head",   [tList (tVar "a")] --> tVar "a");
   ("tail",   [tList (tVar "a")] --> tList (tVar "a"));
   ("take",   [tInt; tList (tVar "a")] --> tList (tVar "a"));
   ("(!!)",   [tList (tVar "a"); tInt] --> tVar "a");
   ("length", [tList (tVar "a")] --> tInt);
   ("(++)",   [tList (tVar "a"); tList (tVar "a")] --> tList (tVar "a"));
   ("filter", [[tVar "a"] --> tBool; tList (tVar "a")]
              --> tList (tVar "a"));
   ("map",    [[tVar "a"] --> tVar "b"; tList (tVar "a")]
              --> tList (tVar "b"));
   ("foldr",  [[tVar "b"; tVar "a"] --> tVar "a";
               tVar "a";
               tList (tVar "b")]
              --> tVar "a");
   ("odd",    [tInt] --> tBool);
   ("even",   [tInt] --> tBool);
   ("(&&)",   [tBool; tBool] --> tBool);
   ("(||)",   [tBool; tBool] --> tBool);
   ("not",    [tBool] --> tBool);
   ("True",   tBool);
   ("False",  tBool);
   ("undefined", tVar "a");
   ("((==)::Int -> Int -> Bool)", [tInt; tInt] --> tBool);
   ("((==)::Bool -> Bool -> Bool)", [tBool; tBool] --> tBool);
   ("((==)::[Int] -> [Int] -> Bool)", [tList tInt; tList tInt] --> tBool);
  ]

let generate_haskell size =
  let weights x = 
    match x with
    | "(!!)" | "[]" -> 1. /. 3.
    | "head" | "tail" -> 1. /. 4.
    | "id" | "undefined" -> 1. /. 10.
    | _ -> 1. in
  let weighted_std_lib =
    List.map (fun entry -> (weights (fst entry), entry)) haskell_std_lib in
  let gen_ty = [tList tInt] --> tList tInt in
  Generate.generate_exp weighted_std_lib size tInt gen_ty
  (* TODO: program stats in debug mode *)

let generate_batch exp_size batch_size =
  Seq.init batch_size
           (fun _ ->
             let p = generate_haskell exp_size in
             Debug.run prerr_newline;
             p)

let generate_file fs =
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
  "codeList = [\n" ^
  "  " ^ String.concat ",\n  " fs ^ "\n" ^
  "  ]\n" ^
  "main = do\n" ^
  "  hSetBuffering stdout NoBuffering\n" ^
  "  forM_ codeList $ \\code -> do\n" ^
  "    forM_ [0..5] $ \\x -> do\n" ^
  "      E.catch (print $ code $ incomplete1 x) handler\n" ^
  "    forM_ [0..5] $ \\x -> do\n" ^
  "      E.catch (print $ code $ incomplete2 x) handler\n" ^
  "    forM_ [0..5] $ \\x -> forM_ [0..x] $ \\y -> do\n" ^
  "      E.catch (print $ code $ incomplete3 x y) handler\n" ^
  "    putStrLn \"====\"\n"

let n = ref 100
let size = ref 25
let seed = ref (-1)

let speclist =
  [
    ("-n", Arg.Set_int n, "Number of functions to generate");
    ("-size", Arg.Set_int size, "Size of each function");
    ("-seed", Arg.Set_int seed, "Random generator seed");
    ("-debug", Arg.Set Debug.debug_mode, "Enable debug mode");
  ]

(* -O -fno-full-laziness *)
let () =
  Arg.parse speclist (fun _ -> ())
    "gen_haskell [-testtype <0>] [-n <100>] [-size <100>] [-seed <-1>";
  (if !seed < 0
   then Random.self_init ()
   else Random.init !seed);

  let fs = Seq.map haskell_string (generate_batch !size !n) in
  print_string (generate_file (List.of_seq fs))
