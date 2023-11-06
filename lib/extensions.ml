(* a wish list of things to go into the standard library *)

(* push element onto a list ref *)
let push x l = l := x :: !l

module Int = struct

  include Int

  let test_bit i j = Int.logand i (Int.shift_left 1 j) <> 0

  (* best I can do without count leading zeros *)
  let log2 x =
    if x <= 0
    then raise (Invalid_argument "Int.log2: argument <= 0");
    let rec lp acc x =
      match x with
      | 0 -> assert false
      | 1 -> acc
      | 2 | 3 -> 1 + acc
      | 4 | 5 | 6 | 7 -> 2 + acc
      | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 -> 3 + acc
      | _ -> lp (4 + acc) (Int.shift_right x 4)
      in
    lp 0 x

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


module Fun = struct

  include Fun

  let curry f x y = f (x, y)
  let uncurry f (x, y) = f x y 

end
