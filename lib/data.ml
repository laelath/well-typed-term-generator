
module DataTy = Key.Make (struct let x="d" end)
type ty = DataTy.t

module DataCon = Key.Make (struct let x="c" end)
type dcon = DataCon.t

  (* let register ... = ... *)

