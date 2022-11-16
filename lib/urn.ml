
type weight = int

type random_sample = weight -> weight

type 'a tree = Node of weight * ('a tree) * ('a tree)
             | Leaf of weight * ('a base)
and 'a base = Value of 'a
            (* lazy nesting *)
            | Nested of (unit -> 'a nested_urn)
and 'a nested_urn = Urn of {size : int; tree : ('a tree) option}

type 'a t = 'a nested_urn

let weight tree =
  match tree with
  | Node (w, _, _) -> w
  | Leaf (w, _) -> w

let empty : 'a nested_urn =
  Urn {size=1; tree=None}

let insert (urn0 : 'a nested_urn) w' a' =
  let Urn {size=size0; tree=tree0} = urn0 in
  match tree0 with
  | None -> Urn {size=1; tree=Some (Leaf (w', a'))}
  | Some tree0 -> 
     let rec insert_rec tree path = 
       match tree with
       | Node (w, l, r) ->
          if path mod 2 = 1
          then Node (w + w', l, insert_rec r (path/2))
          else Node (w + w', insert_rec l (path/2), r)
       | Leaf (w, a) -> Node (w + w', Leaf (w, a), Leaf (w', a'))
     in
     Urn {size=size0+1; tree=Some (insert_rec tree0 size0)}

exception EmptyUrn


let rec sample_opt (rand : random_sample) (urn0 : 'a nested_urn) : 'a option = 
  let Urn {size=_; tree=tree0} = urn0 in
  match tree0 with
  | None -> None
  | Some tree0 -> 
     let rec sample_rec tree i =
       match tree with
       | Leaf (_, base) ->
          (match base with
           | Value a -> a
           | Nested urn ->
              sample rand (urn()))
       | Node (_, l, r) ->
          let wl = weight l in
          if i < wl
          then sample_rec l i
          else sample_rec r (i - wl)
     in
     let sample = rand (weight tree0) in
     Some (sample_rec tree0 sample)

and sample (rand : random_sample) (urn : 'a nested_urn) =
  match sample_opt rand urn with
  | None -> raise EmptyUrn
  | Some a -> a

let uninsert_opt (urn0 : 'a nested_urn) =
  let Urn {size=size0; tree=tree0} = urn0 in
  match tree0 with
  | None -> None
  | Some tree0 ->
     let rec uninsert_rec tree path lb =
       match tree with
       | Leaf (w, base) -> (None, w, base, lb)
       | Node (w, l, r) -> 
          if path mod 2 = 1
          then
            let lb = lb + weight l in
            let (rem, w', a, lb) = uninsert_rec r (path/2) lb in 
            (match rem with
             | None -> (Some l, w', a, lb)
             | Some r -> (Some (Node (w - w', l, r)), w', a, lb))
          else 
            let (rem, w', a, lb) = uninsert_rec l (path/2) lb in 
            (match rem with
             | None -> (Some r, w', a, lb)
             | Some l -> (Some (Node (w - w', l, r)), w', a, lb))
     in
     let (res, w, a, lb) = uninsert_rec tree0 (size0-1) 0 in
     Some (Urn {size=size0; tree=res}, w, a, lb)


let rec replace (tree : 'a tree) (w', a') sample =
  match tree with
  | Leaf (w, base) ->
     (match base with
      | Value a -> (w, a, Leaf (w', a'))
      | Nested _ -> raise Util.Unimplemented)
  | Node (w, l, r) ->
     let wl = weight l in
     if sample < wl
     then let (w_a, a, res) = replace l (w', a') sample in
          (w_a, a, Node (w - w_a + w', res, r))
     else let (w_a, a, res) = replace r (w', a') (sample - wl) in
          (w_a, a, Node (w - w_a + w', l, res))

(*
  remove from urn:
  - sample the urn
    - sampled value:
      get most recent value, 
      replace sampled value with that, 
      remove most recent value
    - sampled nested:
      remove from urn
      if urn is empty, 
      then
      - get most recent value, 
        replace nested urn with that, 
        remove most recent value
      else
      - leave nested urn there

  ok, again
  remove from urn:
    sample the urn
    get the most recent element
    if sampled value is 
    - value
      replace value with most recent
      remove most recent
    - nested
      remove from nested
      if nested now empty
      then
      - replace value with most recent
        remove most recent
      else 
      - nothing
 *)

(*
let rec remove_opt (rand : random_sample) (urn0 : 'a nested_urn) =
  let sample = rand(let Urn {tree=tree0; ...} = urn0 in weight tree0)
  match uninsert_opt urn0 with
  | None -> None
  | Some (urn, w, a, lb) ->
     let Urn {tree; size} = urn in 
     match tree with
     | None -> (a, urn)
     | Some tree ->
        if sample < lb
        then let (_, a, res) = replace tree (w, a) sample in
             (a, Urn {tree=res, size=size})
        else if sample < lb + w
        then (a, urn)
        else let (_, a, res) = replace tree (w, a) (sample - w) in
             (a, Urn {tree=res, size=size})
 *)

(*
let rec remove_opt (rand : random_sample) (urn0 : 'a nested_urn) =
  let Urn {size=size0; tree=tree0} = urn0 in
  match tree0 with
  | None -> None
  | Some tree0 -> 
     let rec remove_rec tree i =
       match tree with
       | Leaf (w, base) ->
          (match base with
           | Value a -> (w, a, None)
           | Nested urn -> 
              let (a, Urn res) = remove rand (urn()) in
              (match res.tree with
               | None -> (w, a, None)
               | Some _ -> (w, a, Some (Leaf (w, Nested (fun () -> Urn res))))
              )
          )
       | Node (w, l, r) ->
          (* this doesn't preserve the balancing *)
          let wl = weight l in
          if i < wl
          then let (w', a, res) = remove_rec l i in
               (match res with
                | Some l -> (w', a, Some (Node (w - w', l, r)))
                | None -> (w', a, Some r)
               )
          else let (w', a, res) = remove_rec r (i - wl) in
               (match res with
                | Some r -> (w', a, Some (Node (w - w', l, r)))
                | None -> (w', a, Some l)
               )
     in
     let sample = rand (weight tree0) in
     let (_, a, res) = remove_rec tree0 sample in
     Some (a, Urn {size=size0-1; tree=res})
 *)
  
(*
and remove (rand : random_sample) (urn : 'a nested_urn) =
  match remove_opt rand urn with
  | None -> raise EmptyUrn
  | Some a -> a
 *)
