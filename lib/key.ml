
module type X_string = sig
  val x : string
end

module type S = sig
  type t
  val reset : unit -> unit
  val make : unit -> t
  val to_string : t -> string
  val equal : t -> t -> bool
  val compare : t -> t -> int
  module Tbl : Hashtbl.S with type key = t
  module Map : Map.S with type key = t
  module Set : Set.S with type elt = t
end

module Make (Prefix : X_string) : S = struct
  type t = int
  let counter = ref 0
  let reset () = counter := 0
  let make () = let c = !counter in
                let () = counter := c + 1 in
                c
  let to_string x = Prefix.x ^ (Int.to_string x)
  let equal = Int.equal
  let compare = Int.compare

  module Tbl = Hashtbl.Make (struct include Int let hash i = i end)
  module Map = Map.Make (Int)
  module Set = Set.Make (Int)

end



