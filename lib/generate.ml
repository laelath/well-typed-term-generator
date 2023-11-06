
open Util

type hole_info = Rules.hole_info

module IntUrn = Urn.Make(Urn.IntWeight)

(*
   MAIN LOOP
 *)
let assert_hole (exp : Exp.exp) =
  match !exp with
  | Exp.Hole _ -> ()
  | _ -> raise (Internal_error "worklist exp is not a hole")


(* TODO: make rules able to decide how to split fuel to children? *)
(* a bit weird in that extension decides to give fuel to
   ext. calls nonlocally *)
let spread_fuel fuel holes =
  let n = List.length holes in
  let fuel_per_hole = Int.max 0 (Int.pred fuel) / Int.max 1 n in
  List.map (fun hole -> (fuel_per_hole, hole)) holes

let generate (step_gens : Generators.t) (fuel0 : int) (ty : External.ty) =
  if not (SS.is_empty (External.ty_vars ty))
  then raise (Invalid_argument "cannot generate polymorphic types");

  let rec lp hole_urn fuel =
    let ((_, hole), urn_opt') = IntUrn.remove hole_urn in
    (* TODO: if rules generate hole_infos, then this check is removed *)
    (*       could also remove env from holes then? *)
    let hole_info =
      match !hole with
      | Exp.Hole (hole_ty, hole_env) ->
         {Rules.hole_exp=hole; hole_ty; hole_env; hole_fuel=fuel}
      | _ -> raise (Internal_error "worklist exp is not a hole") in
    let steps = List.fold_left (fun acc g -> g hole_info @ acc)
                               [] step_gens in
    let (_, step) = Choose.choose steps in
    let holes = step () in
    let fuel' = Int.max 0 (Int.pred fuel) in
    (* TODO: better hole weighting choices *)
    let weighted_holes = spread_fuel hole_info.hole_fuel holes in
    match urn_opt' with
    | Some urn' -> lp (IntUrn.add_list weighted_holes urn') fuel'
    | None ->
       match IntUrn.of_list weighted_holes with
       | None -> ()
       | Some urn' -> lp urn' fuel' in

  let ty = Exp.ty_of_external_ty ty in
  lp (IntUrn.singleton fuel0 (ref (Exp.Hole (ty, [])))) fuel0
