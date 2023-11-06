exception Unimplemented

exception Internal_error of string

module SS = struct

  include Set.Make(String)

  let union_seq =
    Seq.fold_left union empty

end

module SM = struct

  include Map.Make(String)

  let of_string_set f ss =
    of_seq (Seq.map (fun a -> (a, f a)) (SS.to_seq ss))

end
