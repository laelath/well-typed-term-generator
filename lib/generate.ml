
open Util

type hole_info = Rules.hole_info

module IntUrn = Urn.Make(Urn.IntWeight)

(*
   MAIN LOOP
 *)

(* TODO: make rules able to decide how to split fuel to children? *)
(* a bit weird in that extension decides to give fuel to
   arguments of ext. calls nonlocally *)
let spread_fuel fuel holes =
  let n = List.length holes in
  let fuel_per_hole = Int.max 0 (Int.pred fuel) / Int.max 1 n in
  List.map (fun hole -> (Int.succ fuel_per_hole, hole)) holes


let generate_lp
      ?(debug_fun : unit -> unit = Fun.id)
      (steps_gens : Generators.t)
      (holes : Exp.exp IntUrn.t) =
  let rec lp hole_urn =
    Debug.run debug_fun;
    let ((fuel, hole), urn_opt') = IntUrn.remove hole_urn in
    (* TODO: if rules generate hole_infos, then this check is removed *)
    (*       could also remove env from holes then? *)
    let hole_info =
      match !hole with
      | Exp.Hole (hole_ty, hole_env) ->
         {Rules.hole_exp=hole; hole_ty; hole_env;
          hole_fuel=Int.pred fuel}
      | _ -> raise (Internal_error "worklist exp is not a hole") in
    let steps = List.fold_left (fun acc g -> g hole_info @ acc)
                               [] steps_gens in
    let step = Choose.choose_frequency steps in
    let holes = step () in
    (* TODO: better/generalized hole weighting choices *)
    let weighted_holes = spread_fuel hole_info.hole_fuel holes in
    match urn_opt' with
    | Some urn' -> lp (IntUrn.add_list weighted_holes urn')
    | None ->
       (match IntUrn.of_list weighted_holes with
        | None -> ()
        | Some urn' -> lp urn') in
  lp holes


let generate_exp steps_gens (fuel0 : int) uty (ty : External.ty) =
  if not (SS.is_empty (External.ty_vars ty))
  then raise (Invalid_argument "cannot generate polymorphic types");
  let ty = Exp.ty_of_external_ty ty in
  let e = ref (Exp.Hole (ty, [])) in
  let check () = Exp.consistency_check [] e in
  generate_lp ~debug_fun:check steps_gens (IntUrn.singleton fuel0 e);
  Exp.exp_to_external_exp uty e
