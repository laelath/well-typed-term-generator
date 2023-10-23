
(* FIXME *)

type hole_info = {
    label : Exp.exp_label;
    ty_label : Type.ty_label;
    prev : Exp.exp_label option;
    fuel : int;
    vars : (Exp.var * Type.ty_label) list;
    depth : int;
  }

(* BEGIN UTILS *)
(* FIXME: move some into exp.ml? *)

let rec find_pos (prog : Exp.program) (e : Exp.exp_label) (height : int) =
  if height == 0
  then e
  else match (prog.get_exp e).prev with
       | None -> e
       | Some e' -> find_pos prog e' (height - 1)

exception UnresolvedPolymorphism


(* TODO: merge this with Type.flat_ty_to_ty / prog.ty.flat_ty_to_ty *)
let rec ty_label_from_ty (prog : Exp.program) mp ty =
  match ty with
  | Type.FlatTyVar var ->
    (match List.assoc_opt var mp with
     | None -> raise UnresolvedPolymorphism
     | Some tyl -> tyl)
  | Type.FlatTyInt -> prog.ty.new_ty Type.TyInt
  | Type.FlatTyBool -> prog.ty.new_ty Type.TyBool
  | Type.FlatTyList ty' ->
    let tyl' = ty_label_from_ty prog mp ty' in
    prog.ty.new_ty (Type.TyList tyl')
  | Type.FlatTyArrow (tys, ty') ->
    let tyl' = ty_label_from_ty prog mp ty' in
    let tys' = List.map (ty_label_from_ty prog mp) (List.rev tys) in
    prog.ty.new_ty (Type.TyArrow (tys', tyl'))

(* END UTILS *)

(* Implements the rule:
   E ~> E{alpha + tau}
 *)
let extend_extvar (prog : Exp.program) (extvar : Type.extvar) (ext_ty : Type.ty_label) =
  let extend : 'a 'b . Type.extvar -> (Type.extvar -> 'a list) -> ('a -> unit) -> unit =
    fun ext get add ->
    let lst = get ext in
    let handle_elt elt = add elt in
    List.iter handle_elt lst in

  extend extvar prog.ty.extvar_ty_params
         (fun ty_params -> prog.ty.add_ty_param ty_params ext_ty);
  extend extvar prog.extvar_params
         (fun param -> prog.add_param param (prog.new_var()));

  (* Justin: there has to be a better way... *)
  (* Ben: no *)
  let exp_lbls = ref [] in
  extend extvar prog.extvar_args
         (fun arg ->
          let app_lbl = prog.args_parent arg in
          let exp_lbl = prog.new_exp {exp=Exp.Hole; ty=ext_ty; prev=Some app_lbl} in
          prog.add_arg arg exp_lbl;
          exp_lbls := exp_lbl :: !exp_lbls);

  !exp_lbls


(* Implements the rule:
   E_1[lambda_i xs alpha . E_2[<>]] ~>
   E_1{alpha + tau}[lambda_i (x::xs) alpha . E_2{alpha + tau}[x]]

   via the decomposition

   E_1[lambda_i xs alpha . E_2[<>]] ~>
   E_1{alpha + tau}[lambda_i (x::xs) alpha . E_2{alpha+tau}[<>]] ~>
   E_1{alpha + tau}[lambda_i (x::xs) alpha . E_2{alpha + tau}[x]]
 *)
let not_useless_step (prog : Exp.program) (hole : hole_info) param =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("extending ext. var\n"));
  let extvar = prog.params_extvar param in
  let holes = extend_extvar prog extvar hole.ty_label in
  let x = List.hd (prog.get_params param) in
  prog.set_exp hole.label {exp=Exp.Var x; ty=hole.ty_label; prev=hole.prev};
  holes


(* Implements the rule:
   E[<>] ~> E[call <> alpha] where alpha is fresh
 *)
let ext_function_call_step (prog : Exp.program) (hole : hole_info)  =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("creating ext. function call\n"));
  let extvar = prog.new_extvar() in
  let f_ty = prog.ty.new_ty (Type.TyArrowExt (prog.ty.new_ty_params extvar, hole.ty_label)) in
  let f = prog.new_exp {exp=Exp.Hole; ty=f_ty; prev=Some hole.label} in
  let args = prog.new_args extvar hole.label in
  prog.set_exp hole.label {exp=Exp.ExtCall (f, args); ty=hole.ty_label; prev=hole.prev};
  [f]



(* Implements the rule:
   E[<>] ~> E[call f <> ... alpha] where f is in alpha
 *)
let palka_rule_step (prog : Exp.program) (hole : hole_info) (f, f_ty) =
  fun () ->
  match (prog.ty.get_ty f_ty) with
  | Type.TyArrowExt (ty_params, _) ->
     Debug.run (fun () -> Printf.eprintf ("creating palka ext. function call\n"));
     let fe = prog.new_exp {exp=Exp.Var f; ty=f_ty; prev=Some hole.label} in
     let extvar = prog.ty.ty_params_extvar ty_params in
     let args = prog.new_args extvar hole.label in
     let holes = List.map (fun arg_ty ->
                     let hole = prog.new_exp {exp=Exp.Hole; ty=arg_ty; prev=Some hole.label} in
                     prog.add_arg args hole;
                     hole)
                          (List.rev (prog.ty.get_ty_params ty_params)) in
     prog.set_exp hole.label {exp=Exp.ExtCall (fe, args); ty=hole.ty_label; prev=hole.prev};
     holes
  | Type.TyArrow (tys, _) ->
     Debug.run (fun () -> Printf.eprintf ("creating palka function call\n"));
     let fe = prog.new_exp {exp=Exp.Var f; ty=f_ty; prev=Some hole.label} in
     let holes = List.map (fun arg_ty -> prog.new_exp {exp=Exp.Hole; ty=arg_ty; prev=Some hole.label}) tys in
     prog.set_exp hole.label {exp=Exp.Call (fe, holes); ty=hole.ty_label; prev=hole.prev};
     holes
  | _ -> raise (Util.Impossible "variable in function list not a function")


(* Implements the rule:
   FIXME
   E[<>] ~>
 *)
let let_insertion_step (prog : Exp.program) (hole : hole_info) height =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("inserting let\n"));
  let e' = find_pos prog hole.label height in
  let node' = prog.get_exp e' in
  let x = prog.new_var () in
  let e_let = prog.new_exp {exp=Exp.Hole; ty=node'.ty; prev=node'.prev} in
  let e_hole = prog.new_exp {exp=Exp.Hole; ty=hole.ty_label; prev=Some e_let} in
  prog.set_exp e_let {exp=Exp.Let (x, e_hole, e'); ty=node'.ty; prev=node'.prev};
  prog.set_exp e' {exp=node'.exp; ty=node'.ty; prev=Some e_let};
  (match node'.prev with
   | None -> prog.head <- e_let
   | Some e'' -> prog.rename_child (e', e_let) e'');
  let node = prog.get_exp hole.label in
  prog.set_exp hole.label {exp=Exp.Var x; ty=node.ty; prev=node.prev};
  [e_hole]


(* TODO: reduce redundancy *)
(* Implements the rule:
   FIXME
   E[<>] ~>
 *)
let match_insertion_step (prog : Exp.program) (hole : hole_info) height =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("inserting match (fst)\n"));
  let e' = find_pos prog hole.label height in
  let node' = prog.get_exp e' in
  let e_match = prog.new_exp {exp=Exp.Hole; ty=node'.ty; prev=node'.prev} in
  let hole_nil = prog.new_exp {exp=Exp.Hole; ty=node'.ty; prev=Some e_match} in
  let list_ty = prog.ty.new_ty (Type.TyList hole.ty_label) in
  let hole_scr = prog.new_exp {exp=Exp.Hole; ty=list_ty; prev=Some e_match} in
  let x = prog.new_var () in
  let y = prog.new_var () in
  prog.set_exp e_match {exp=Exp.Match (hole_scr, hole_nil, (x, y, e')); ty=node'.ty; prev=node'.prev};
  prog.set_exp e' {exp=node'.exp; ty=node'.ty; prev=Some e_match};
  (match node'.prev with
   | None -> prog.head <- e_match
   | Some e'' -> prog.rename_child (e', e_match) e'');
  let node = prog.get_exp hole.label in
  prog.set_exp hole.label {exp=Exp.Var x; ty=node.ty; prev=node.prev};
  [hole_scr; hole_nil]

(* Implements the rule:
   FIXME
   E[<>] ~>
 *)
let match_insertion_list_step (prog : Exp.program) (hole : hole_info) height =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("inserting match (rst)\n"));
  let e' = find_pos prog hole.label height in
  let node' = prog.get_exp e' in
  let e_match = prog.new_exp {exp=Exp.Hole; ty=node'.ty; prev=node'.prev} in
  let hole_nil = prog.new_exp {exp=Exp.Hole; ty=node'.ty; prev=Some e_match} in
  let hole_scr = prog.new_exp {exp=Exp.Hole; ty=hole.ty_label; prev=Some e_match} in
  let x = prog.new_var () in
  let y = prog.new_var () in
  prog.set_exp e_match {exp=Exp.Match (hole_scr, hole_nil, (x, y, e')); ty=node'.ty; prev=node'.prev};
  prog.set_exp e' {exp=node'.exp; ty=node'.ty; prev=Some e_match};
  (match node'.prev with
   | None -> prog.head <- e_match
   | Some e'' -> prog.rename_child (e', e_match) e'');
  let node = prog.get_exp hole.label in
  prog.set_exp hole.label {exp=Exp.Var y; ty=node.ty; prev=node.prev};
  [hole_scr; hole_nil]


(* Implements the rule:
   FIXME
   E[<>] ~>
 *)
let create_match_step (prog : Exp.program) (hole : hole_info) (x, ty) =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("creating match\n"));
  let e_scr = prog.new_exp {exp=Exp.Var x; ty=ty; prev=Some hole.label} in
  let e_empty = prog.new_exp {exp=Exp.Hole; ty=hole.ty_label; prev=Some hole.label} in
  let e_cons = prog.new_exp {exp=Exp.Hole; ty=hole.ty_label; prev=Some hole.label} in
  prog.set_exp hole.label
               {exp=Exp.Match (e_scr, e_empty, (prog.new_var (), prog.new_var (), e_cons));
                ty=hole.ty_label; prev=hole.prev};
  [e_empty; e_cons]



(* Implements the rule:
   E[<>] ~> E[x]
 *)
(* TODO: increase the chance of variable reference for complex types? *)
let var_step (prog : Exp.program) (hole : hole_info) (var, _) =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("creating var reference\n"));
  prog.set_exp hole.label {exp=Exp.Var var; ty=hole.ty_label; prev=hole.prev};
  []


(* Implements the rule:
   FIXME
   E[<>] ~>
 *)
let create_if_step (prog : Exp.program) (hole : hole_info)  =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("creating if\n"));
  let pred = prog.new_exp {exp=Exp.Hole; ty=prog.ty.new_ty Type.TyBool; prev=Some hole.label} in
  let thn = prog.new_exp {exp=Exp.Hole; ty=hole.ty_label; prev=Some hole.label} in
  let els = prog.new_exp {exp=Exp.Hole; ty=hole.ty_label; prev=Some hole.label} in
  prog.set_exp hole.label {exp=Exp.If (pred, thn, els); ty=hole.ty_label; prev=hole.prev};
  [pred; thn; els]



(* Implements the rule:
   FIXME
   E[<>] ~>
 *)
let std_lib_step (prog : Exp.program) (hole : hole_info) x =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("creating std lib reference: %s\n") x);
  prog.set_exp hole.label {exp=Exp.StdLibRef x; ty=hole.ty_label; prev=hole.prev};
  []


(* Implements the rule:
   FIXME
   E[<>] ~>
 *)
let std_lib_palka_rule_step (prog : Exp.program) (hole : hole_info) (f, ty, tys, mp) =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("creating std lib palka call: %s\n") f);
  let vars = List.fold_left Util.SS.union (Type.ty_vars ty) (List.map Type.ty_vars tys) in
  let unmapped_vars = Util.SS.diff vars (Util.SS.of_list (List.map fst mp)) in
  let mp' = List.map (fun x -> (x, Old.random_type hole.fuel prog)) (Util.SS.elements unmapped_vars) in
  let tyls = List.map (ty_label_from_ty prog (mp' @ mp)) (List.rev tys) in
  let holes = List.map (fun tyl -> prog.new_exp {exp=Exp.Hole; ty=tyl; prev=Some hole.label}) tyls in
  let func = prog.new_exp {exp=Exp.StdLibRef f; ty=prog.ty.new_ty (Type.TyArrow (tyls, hole.ty_label)); prev=Some hole.label} in
  prog.set_exp hole.label {exp=Exp.Call (func, holes); ty=hole.ty_label; prev=hole.prev};
  holes


(* Implements the rule:
   E[<>] ~> E[value]
 *)
let base_constructor_step (prog : Exp.program) (hole : hole_info) exp' =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("Creating base constructor\n"));
  prog.set_exp hole.label {exp=exp'; ty=hole.ty_label; prev=hole.prev};
  []
  (*match prog.ty.get_ty hole.ty_label with
  | TyInt ->
     fun () ->
     set exp'; []
  | _ -> raise (Util.Impossible "bad base type")*)


(* Implements the rule:
   E[<>] ~> E[dcon <> ... <>]
 *)
let data_constructor_step (prog : Exp.program) (hole : hole_info) dcon =
  let set exp = prog.set_exp hole.label {exp=exp; ty=hole.ty_label; prev=hole.prev} in
  match prog.ty.get_ty hole.ty_label with
  (*| TyBool ->
     (match dcon with
      | "true" ->
         fun () ->
         Debug.run (fun () -> Printf.eprintf ("creating true\n"));
         set (Exp.ValBool true);
         []
      | "false" ->
         fun () ->
         Debug.run (fun () -> Printf.eprintf ("creating false\n"));
         set (Exp.ValBool true);
         []
     | _ -> raise (Util.Impossible "bad data constructor"))*)
  | TyList ty' ->
     (match dcon with
      | "nil" ->
         fun () ->
         Debug.run (fun () -> Printf.eprintf ("creating nil\n"));
         set (Exp.Empty);
         []
      | "cons" ->
         fun () ->
         Debug.run (fun () -> Printf.eprintf ("creating cons\n"));
         let lhole = prog.new_exp {exp=Exp.Hole; ty=hole.ty_label; prev=Some hole.label} in
         let ehole = prog.new_exp {exp=Exp.Hole; ty=ty'; prev=Some hole.label} in
         set (Exp.Cons (ehole, lhole));
         [ehole; lhole]
      | _ -> raise (Util.Impossible "bad data constructor"))
  | _ -> raise (Util.Impossible "data constructor on non-data type")


(* Implements the rule:
   E[<>] ~> E[lambda ... <>]
 *)
let func_constructor_step (prog : Exp.program) (hole : hole_info) =
  let set exp = prog.set_exp hole.label {exp=exp; ty=hole.ty_label; prev=hole.prev} in
  match prog.ty.get_ty hole.ty_label with
  | TyArrow (ty_params, ty') ->
     fun () ->
     Debug.run (fun () -> Printf.eprintf ("creating lambda\n"));
     let xs = List.map (fun _ -> prog.new_var ()) ty_params in
     let body = prog.new_exp {exp=Exp.Hole; ty=ty'; prev=Some hole.label} in
     set (Exp.Lambda (xs, body));
     [body]
  | TyArrowExt (ty_params, ty') ->
     fun () ->
     Debug.run (fun () -> Printf.eprintf ("creating ext. lambda\n"));
     let extvar = prog.ty.ty_params_extvar ty_params in
     let params = prog.new_params extvar in
     let xs = List.map (fun _ -> prog.new_var ()) (prog.ty.get_ty_params ty_params) in
     List.iter (prog.add_param params) xs;
     let body = prog.new_exp {exp=Exp.Hole; ty=ty'; prev=Some hole.label} in
     set (Exp.ExtLambda (params, body));
     [body]
  | _ -> fun () ->
         raise (Util.Impossible "function constructor on non-function type")

let application_step (prog : Exp.program) (hole : hole_info) tys =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("creating application\n"));
  let func = prog.new_exp {exp=Exp.Hole;
                           ty=prog.ty.new_ty (TyArrow (tys, hole.ty_label));
                           prev=Some hole.label} in
  let args = List.map (fun ty -> prog.new_exp {exp=Exp.Hole;
                                               ty=ty;
                                               prev=Some hole.label}) tys in
  let holes = [func] @ args in
  prog.set_exp hole.label {exp=Exp.Call (func, args); ty=hole.ty_label; prev=hole.prev};
  holes

let seq_step (prog : Exp.program) (hole : hole_info) (var : Exp.var * Type.ty_label) =
  fun () ->
  Debug.run (fun () -> Printf.eprintf ("creating palka seq\n"));
  let seq = prog.new_exp {exp=Exp.StdLibRef "seq";
                          ty=prog.ty.new_ty (TyArrow ([hole.ty_label; snd var], hole.ty_label));
                          prev=Some hole.label} in
  let ref = prog.new_exp {exp=Exp.Var (fst var);
                          ty=snd var;
                          prev=Some hole.label} in
  let hole' = prog.new_exp {exp=Exp.Hole;
                           ty=hole.ty_label;
                           prev=Some hole.label} in
  prog.set_exp hole.label {exp=Exp.Call (seq, [hole'; ref]); ty=hole.ty_label; prev=hole.prev};
  [hole']
