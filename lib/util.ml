exception Unimplemented

exception Impossible of string

exception ConsistencyError of string

module SS = Set.Make(String)
module SM = Map.Make(String)

let union_map f =
  List.fold_left (fun acc x -> SS.union acc (f x)) SS.empty

let sm_of_ss f ss =
  SM.of_seq (Seq.map (fun a -> (a, f a)) (SS.to_seq ss))
