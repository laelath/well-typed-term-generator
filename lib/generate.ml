(* Each node has a unique label, which cannot be changed.
   if we have some node (call e1_l1 e2_l2) and we are updating e1 to (let (x rhs) e1),
   it's tempting to overwrite the l1 label to point to this new node.
   The problem is that we have update maps `type extension var -> program location set`
   that point to where syntactic updates need to happen, and we don't want to update these.

   Each node also has a `prev` pointer, so there's no term sharing
   allowed; each node has exactly one reference.
 *)

type worklist = {
    pop : unit -> Exp.exp_label option;
    add : int * Exp.exp_label-> unit;
  }
type state = {
    worklist : worklist;
    mutable fuel : int;
  }

type hole_info = Rules.hole_info

let make_state (fuel : int) : state =
  let holes = ref [] in
  let pop () =
    match !holes with
    | [] -> None
    | h ->
       let (hole, holes') = Choose.choose_frequency_split h in
       holes := holes';
       Some hole in
  let add e = holes := e :: !holes in
  {
    fuel = fuel;
    worklist = {
      pop = pop;
      add = add
    }
  }

(*
   MAIN LOOP
 *)

let assert_hole (exp : Exp.exp) =
  match exp with
  | Exp.Hole -> ()
  | _ -> raise (Util.InternalError "exp is not a hole")

let sample n = Random.int n

let generate_exp (steps : Generators.t) (fuel : int) (prog : Exp.program) (e : Exp.exp_label) =
  let node = prog.get_exp e in
  Debug.run (fun () -> assert_hole node.exp);
  let hole : hole_info = {
    label=e;
    ty_label=node.ty;
    prev=node.prev;
    fuel=fuel;
    vars=Generators.find_vars prog e;
    depth=Generators.exp_depth prog e;
  } in
  let steps = List.fold_left (fun acc g -> g prog hole acc) Urn.empty steps in
  (Urn.sample sample steps) ()

let generate (steps : Generators.t) (st : state) (prog : Exp.program) : bool =
  match st.worklist.pop () with
  | None -> false
  | Some e ->
    let holes = generate_exp steps st.fuel prog e in
    List.iter (fun hole -> st.worklist.add (st.fuel + 1, hole)) holes;
    Debug.run (fun () -> Exp.check prog);
    st.fuel <- if st.fuel > 0 then st.fuel - 1 else 0;
    true

let generate_fp (steps : Generators.t) ?(std_lib = []) (size : int) (ty : Exp.ty) : Exp.program =
  let prog = Exp.make_program ~std_lib: std_lib ty in
  let st = make_state size in
  st.worklist.add (st.fuel, prog.head);
  let rec lp () =
    match generate steps st prog with
    | false -> prog
    | true -> lp() in
  lp()
