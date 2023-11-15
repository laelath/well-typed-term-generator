(* Implements the creation of "almost perfect" binary trees *)

open Extensions

(* TODO: Antal says this can be more efficient
         (but didn't implement a more efficient version) *)
let reverse_bits =
  let rec go r n x =
    match n with
    | 0 -> r
    | _ -> go (Int.logor (Int.shift_left r 1) (Int.logand x 1))
              (Int.pred n)
              (Int.shift_right x 1) in
  go 0

let almost_perfect node leaf size elems0 =
  let perfect_depth = Int.log2 size in
  let remainder = size - Int.shift_left 1 perfect_depth in
  let raise_size_error () =
    invalid_arg
      ("almost_perfect: size mismatch: got input of length " ^
       Int.to_string (NonEmpty.length elems0) ^
       ", but expected size " ^ Int.to_string size) in
  let rec go depth index elems =
    match depth with
    | 0 ->
       if reverse_bits perfect_depth index < remainder
       then (match elems with
             | l :: r :: elems' ->
                (node (leaf l) (leaf r), elems', Int.succ index)
             | _ -> raise_size_error ())
       else (match elems with
             | x :: elems' ->
                (leaf x, elems', Int.succ index)
             | _ -> raise_size_error ())
    | _ ->
      let (l, elems',  index' ) = go (Int.pred depth) index  elems  in
      let (r, elems'', index'') = go (Int.pred depth) index' elems' in
      (node l r, elems'', index'') in
  let (tree, _, _) = go perfect_depth 0 (NonEmpty.to_list elems0) in
  tree

