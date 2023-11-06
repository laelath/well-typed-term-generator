(* a wish list of things to go into the standard library *)

(* push element onto a list ref *)
let push x l = l := x :: !l

module Int = struct

  include Int

  let test_bit i j = Int.logand i (Int.shift_left 1 j) <> 0

  (* TODO: better version? *)
  let rec log2 x =
    match x with
    | 1 -> 0
    | _ -> 1 + log2 ((x + 1) / 2)

end

(* non-empty lists *)
(* stores the first element unlike haskell,
   but I think that makes more sense for strict evaluation *)
(* TODO: could have a field day duplicating list functions *)
module NonEmpty = struct

  type 'a t = Head of 'a * 'a list

  let of_list l =
    match l with
    | [] -> None
    | h :: t -> Some (Head (h, t))

  let to_list (Head (h, t)) = h :: t

  let length (Head (_, t)) = 1 + List.length t

  let singleton x = Head (x, [])
  let cons x (Head (h, t)) = Head (x, h :: t)

  let hd (Head (h, _)) = h
  let tl (Head (_, t)) = t

end

type 'a nonempty = 'a NonEmpty.t
