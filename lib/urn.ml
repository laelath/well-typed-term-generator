
type weight = int

type random_sample = weight -> weight

type 'a tree = Node of weight * ('a tree) * ('a tree)
             | Leaf of weight * ('a base)
and 'a base = Value of 'a
            (* lazy nesting *)
            | Nested of (unit -> 'a nested_urn)
and 'a nested_urn = Urn of {size : int; tree : ('a tree) option}

let weight tree =
  match tree with
  | Node (w, _, _) -> w
  | Leaf (w, _) -> w

exception EmptyUrn

let rec sample (rand : random_sample) (urn0 : 'a nested_urn) = 
  let Urn {size=_; tree=tree0} = urn0 in
  match tree0 with
  | None -> raise EmptyUrn
  | Some tree0 -> 
     let rec sample_rec tree i =
       match tree with
       | Leaf (_, base) ->
          (match base with
           | Value a -> a
           | Nested urn -> sample rand (urn()))
       | Node (_, l, r) ->
          let wl = weight l in
          if i < wl
          then sample_rec l i
          else sample_rec r (i - wl)
     in
     let sample = rand (weight tree0) in
     sample_rec tree0 sample

let empty : 'a nested_urn =
  Urn {size=1; tree=None}

let insert (urn0 : 'a nested_urn) w' a' =
  let Urn {size=size0; tree=tree0} = urn0 in
  match tree0 with
  | None -> Urn {size=1; tree=Some (Leaf (w', a'))}
  | Some tree0 -> 
     let rec insert_rec tree size = 
       match tree with
       | Node (w, l, r) ->
          if size mod 2 = 0
          then Node (w + w', l, insert_rec r (size/2))
          else Node (w + w', insert_rec l (size/2), r)
       | Leaf (w, a) -> Node (w + w', Leaf (w, a), Leaf (w', a'))
     in
     Urn {size=size0+1; tree=Some (insert_rec tree0 size0)}
